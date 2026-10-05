import unittest
from pathlib import Path

import rowl

ROOT = Path(__file__).resolve().parents[3]
MEDICATION = ROOT / "examples" / "medication-safety.ofn"
MEDICATION_NT = ROOT / "examples" / "medication-safety.nt"
IRI = "https://example.org/medication/"


class MedicationSafety(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reasoner = rowl.Reasoner.from_file(MEDICATION)

    @classmethod
    def tearDownClass(cls):
        cls.reasoner.close()

    def test_consistent(self):
        self.assertIs(self.reasoner.consistent(), True)

    def test_allergy_alerts(self):
        alert = IRI + "AllergyAlert"
        self.assertIs(self.reasoner.instance_of(IRI + "alice", alert), True)
        self.assertIs(self.reasoner.instance_of(IRI + "bob", alert), False)
        self.assertIs(self.reasoner.instance_of(IRI + "carol", alert), False)

    def test_subsumption(self):
        self.assertIs(self.reasoner.subsumed(IRI + "Amoxicillin", IRI + "Penicillin"), True)
        self.assertIs(self.reasoner.subsumed(IRI + "Penicillin", IRI + "Amoxicillin"), False)
        self.assertIs(self.reasoner.satisfiable(IRI + "Penicillin"), True)

    def test_names(self):
        self.assertIn(IRI + "Penicillin", self.reasoner.classes())
        self.assertIn(IRI + "alice", self.reasoner.individuals())

    def test_classification_matches_pairwise_questions(self):
        classified = self.reasoner.classify()
        self.assertIsNotNone(classified)
        names = self.reasoner.classes()
        self.assertEqual([entry.iri for entry in classified], names)
        for entry in classified:
            self.assertIs(self.reasoner.satisfiable(entry.iri), entry.satisfiable)
            if not entry.satisfiable:
                continue
            for other in names:
                if other != entry.iri:
                    self.assertIs(self.reasoner.subsumed(entry.iri, other), other in entry.superclasses)
        self.assertEqual(self.reasoner.superclasses(IRI + "Azithromycin"), [IRI + "Macrolide"])


class NTriples(unittest.TestCase):
    def test_same_answers_as_functional_syntax(self):
        with rowl.Reasoner.from_file(MEDICATION) as functional, \
                rowl.Reasoner.from_file(MEDICATION_NT) as triples:
            self.assertEqual(triples.classes(), functional.classes())
            self.assertEqual(triples.individuals(), functional.individuals())
            self.assertEqual(triples.classify(), functional.classify())
            alert = IRI + "AllergyAlert"
            for person in ["alice", "bob", "carol"]:
                self.assertIs(triples.instance_of(IRI + person, alert),
                              functional.instance_of(IRI + person, alert))

    def test_rejected_and_unmapped_graphs(self):
        with self.assertRaises(rowl.DocumentRejected):
            rowl.Reasoner("<a> <b> .", syntax="ntriples")
        undeclared = "<https://example.org/a> <https://example.org/p> <https://example.org/b> .\n"
        with self.assertRaises(rowl.DocumentRejected):
            rowl.Reasoner(undeclared, syntax="ntriples")
        with self.assertRaises(ValueError):
            rowl.Reasoner("", syntax="turtle")


class Errors(unittest.TestCase):
    def test_rejected_document(self):
        with self.assertRaises(rowl.DocumentRejected):
            rowl.Reasoner("Ontology(")

    def test_closed_reasoner(self):
        reasoner = rowl.Reasoner.from_file(MEDICATION)
        reasoner.close()
        with self.assertRaises(ValueError):
            reasoner.consistent()

    def test_context_manager_and_version(self):
        with rowl.Reasoner(MEDICATION.read_text()) as reasoner:
            self.assertIs(reasoner.consistent(), True)
        self.assertEqual(rowl.library_version(), "0.0.0")

    def test_iris_must_be_text(self):
        with rowl.Reasoner.from_file(MEDICATION) as reasoner:
            with self.assertRaises(TypeError):
                reasoner.satisfiable(42)


if __name__ == "__main__":
    unittest.main()
