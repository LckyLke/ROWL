import unittest
from pathlib import Path

import rowl

ROOT = Path(__file__).resolve().parents[3]
MEDICATION = ROOT / "examples" / "medication-safety.ofn"
MEDICATION_NT = ROOT / "examples" / "medication-safety.nt"
MEDICATION_TTL = ROOT / "examples" / "medication-safety.ttl"
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
            rowl.Reasoner("", syntax="rdfxml")


class Turtle(unittest.TestCase):
    def test_same_answers_as_functional_syntax(self):
        with rowl.Reasoner.from_file(MEDICATION) as functional, \
                rowl.Reasoner.from_file(MEDICATION_TTL) as turtle:
            self.assertEqual(turtle.classes(), functional.classes())
            self.assertEqual(turtle.individuals(), functional.individuals())
            self.assertEqual(turtle.classify(), functional.classify())
            alert = IRI + "AllergyAlert"
            for person in ["alice", "bob", "carol"]:
                self.assertIs(turtle.instance_of(IRI + person, alert),
                              functional.instance_of(IRI + person, alert))

    def test_rejected_and_unmapped_graphs(self):
        with self.assertRaises(rowl.DocumentRejected):
            rowl.Reasoner("<a> <b> <c> .", syntax="turtle")
        undeclared = "@prefix ex: <https://example.org/> .\nex:a ex:p ex:b .\n"
        with self.assertRaises(rowl.DocumentRejected):
            rowl.Reasoner(undeclared, syntax="turtle")


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


class Validity(unittest.TestCase):
    def test_examples_are_owl_2_dl(self):
        for example in (MEDICATION, MEDICATION_NT):
            with rowl.Reasoner.from_file(example) as reasoner:
                self.assertIsNone(reasoner.dl_violation())

    def test_first_violation_is_reported(self):
        text = ("Prefix(:=<https://example.org/>)\n"
                "Ontology(<https://example.org/o>\nSubClassOf(:A :B))\n")
        with rowl.Reasoner(text) as reasoner:
            self.assertEqual(
                reasoner.dl_violation(),
                "https://example.org/A is used as a class but not declared as one "
                "(typing constraints, §5.8.1)")


PRESCRIPTIONS = ROOT / "examples" / "imports" / "medication-prescriptions.ofn"


class ImportClosures(unittest.TestCase):
    def test_split_example_gives_the_same_answers(self):
        alert = IRI + "AllergyAlert"
        with rowl.Reasoner.from_file(PRESCRIPTIONS, imports=[PRESCRIPTIONS.parent]) as closure, \
                rowl.Reasoner.from_file(MEDICATION) as whole:
            for person in ("alice", "bob", "carol"):
                self.assertIs(closure.instance_of(IRI + person, alert),
                              whole.instance_of(IRI + person, alert))
            self.assertIs(closure.instance_of(IRI + "alice", alert), True)
            self.assertEqual(closure.classes(), whole.classes())
            self.assertIsNone(closure.dl_violation())
        with rowl.Reasoner.from_file(PRESCRIPTIONS) as alone:
            self.assertIn("not declared", alone.dl_violation())

    def test_missing_and_ambiguous_imports_are_named(self):
        with self.assertRaises(rowl.ImportUnresolved) as raised:
            rowl.Reasoner.from_file(PRESCRIPTIONS, imports=[])
        self.assertIn("https://example.org/medication/vocabulary/1.0", str(raised.exception))
        vocabulary = PRESCRIPTIONS.parent / "medication-vocabulary.ttl"
        with self.assertRaises(rowl.ImportUnresolved):
            rowl.Reasoner.from_file(PRESCRIPTIONS, imports=[vocabulary, vocabulary])

    def test_documents_from_text_keep_node_ids_apart(self):
        first = ("Prefix(:=<http://example.org/>)\n"
                 "Ontology(<http://example.org/first> Import(<http://example.org/second>)\n"
                 "Declaration(Class(:A)) Declaration(Class(:B)) DisjointClasses(:A :B)\n"
                 "ClassAssertion(:A _:x))\n")
        second = ("Prefix(:=<http://example.org/>)\n"
                  "Ontology(<http://example.org/second> ClassAssertion(:B _:x))\n")
        with rowl.Reasoner.from_documents([("first", first, "functional"),
                                           ("second", second, "functional")]) as closure:
            self.assertIs(closure.consistent(), True)
        with self.assertRaises(rowl.DocumentRejected) as raised:
            rowl.Reasoner.from_documents([("first", first, "functional"), ("broken", "Ontology(", "functional")])
        self.assertIn("broken", str(raised.exception))
