import Rowl.Rdf
import Rowl.Decimal
import Rowl.Nnf

/-!
The forward mapping from OWL 2 ontologies to RDF graphs (OWL 2 Mapping to RDF
Graphs, 2012, §2), for axioms and annotations without annotations of their own,
and the proof that `rdf_mapping::map_graph` reads graphs back exactly: whenever
it returns an ontology, the forward mapping of that ontology, with the blank
nodes it returns, is the input graph.

The forward mapping is stated as inductive relations independent of the Rust
code. A triple is compared through views: an IRI by its spelling, a blank node
as it is, a literal by its lexical form and its datatype IRI or language tag.
`Supply` is the list of blank nodes the mapping allocates, in order: an
expression takes its own node first, then its parts from left to right, and an
RDF list takes all its cells before its elements. A structural literal of type
`rdf:PlainLiteral` maps to the RDF 1.1 literal with the language tag after its
last `@`, or to an `xsd:string` literal when that tag is empty, and a
cardinality to the canonical `xsd:nonNegativeInteger` spelling of its value.
-/
namespace Rowl.RdfMapping
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust

/-- `rdf:type` -/
def rdfType : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 116#u8, 121#u8, 112#u8, 101#u8]
/-- `rdf:first` -/
def rdfFirst : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 102#u8, 105#u8, 114#u8, 115#u8, 116#u8]
/-- `rdf:rest` -/
def rdfRest : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 114#u8, 101#u8, 115#u8, 116#u8]
/-- `rdf:nil` -/
def rdfNil : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 110#u8, 105#u8, 108#u8]
/-- `rdf:PlainLiteral` -/
def rdfPlainLiteral : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 49#u8, 57#u8, 57#u8, 57#u8, 47#u8, 48#u8, 50#u8, 47#u8, 50#u8, 50#u8, 45#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 121#u8, 110#u8, 116#u8, 97#u8, 120#u8, 45#u8, 110#u8, 115#u8, 35#u8, 80#u8, 108#u8, 97#u8, 105#u8, 110#u8, 76#u8, 105#u8, 116#u8, 101#u8, 114#u8, 97#u8, 108#u8]
/-- `rdfs:subClassOf` -/
def rdfsSubClassOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 117#u8, 98#u8, 67#u8, 108#u8, 97#u8, 115#u8, 115#u8, 79#u8, 102#u8]
/-- `rdfs:subPropertyOf` -/
def rdfsSubPropertyOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 117#u8, 98#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8, 79#u8, 102#u8]
/-- `rdfs:domain` -/
def rdfsDomain : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 100#u8, 111#u8, 109#u8, 97#u8, 105#u8, 110#u8]
/-- `rdfs:range` -/
def rdfsRange : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 114#u8, 97#u8, 110#u8, 103#u8, 101#u8]
/-- `rdfs:Datatype` -/
def rdfsDatatype : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 48#u8, 47#u8, 48#u8, 49#u8, 47#u8, 114#u8, 100#u8, 102#u8, 45#u8, 115#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 68#u8, 97#u8, 116#u8, 97#u8, 116#u8, 121#u8, 112#u8, 101#u8]
/-- `owl:Class` -/
def owlClass : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 67#u8, 108#u8, 97#u8, 115#u8, 115#u8]
/-- `owl:Restriction` -/
def owlRestriction : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 82#u8, 101#u8, 115#u8, 116#u8, 114#u8, 105#u8, 99#u8, 116#u8, 105#u8, 111#u8, 110#u8]
/-- `owl:Ontology` -/
def owlOntology : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 79#u8, 110#u8, 116#u8, 111#u8, 108#u8, 111#u8, 103#u8, 121#u8]
/-- `owl:versionIRI` -/
def owlVersionIRI : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 118#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8, 73#u8, 82#u8, 73#u8]
/-- `owl:imports` -/
def owlImports : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 105#u8, 109#u8, 112#u8, 111#u8, 114#u8, 116#u8, 115#u8]
/-- `owl:ObjectProperty` -/
def owlObjectProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 79#u8, 98#u8, 106#u8, 101#u8, 99#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:DatatypeProperty` -/
def owlDatatypeProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 68#u8, 97#u8, 116#u8, 97#u8, 116#u8, 121#u8, 112#u8, 101#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:AnnotationProperty` -/
def owlAnnotationProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 65#u8, 110#u8, 110#u8, 111#u8, 116#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:NamedIndividual` -/
def owlNamedIndividual : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 78#u8, 97#u8, 109#u8, 101#u8, 100#u8, 73#u8, 110#u8, 100#u8, 105#u8, 118#u8, 105#u8, 100#u8, 117#u8, 97#u8, 108#u8]
/-- `owl:equivalentClass` -/
def owlEquivalentClass : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 101#u8, 113#u8, 117#u8, 105#u8, 118#u8, 97#u8, 108#u8, 101#u8, 110#u8, 116#u8, 67#u8, 108#u8, 97#u8, 115#u8, 115#u8]
/-- `owl:disjointWith` -/
def owlDisjointWith : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 100#u8, 105#u8, 115#u8, 106#u8, 111#u8, 105#u8, 110#u8, 116#u8, 87#u8, 105#u8, 116#u8, 104#u8]
/-- `owl:disjointUnionOf` -/
def owlDisjointUnionOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 100#u8, 105#u8, 115#u8, 106#u8, 111#u8, 105#u8, 110#u8, 116#u8, 85#u8, 110#u8, 105#u8, 111#u8, 110#u8, 79#u8, 102#u8]
/-- `owl:propertyChainAxiom` -/
def owlPropertyChainAxiom : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 112#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8, 67#u8, 104#u8, 97#u8, 105#u8, 110#u8, 65#u8, 120#u8, 105#u8, 111#u8, 109#u8]
/-- `owl:equivalentProperty` -/
def owlEquivalentProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 101#u8, 113#u8, 117#u8, 105#u8, 118#u8, 97#u8, 108#u8, 101#u8, 110#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:propertyDisjointWith` -/
def owlPropertyDisjointWith : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 112#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8, 68#u8, 105#u8, 115#u8, 106#u8, 111#u8, 105#u8, 110#u8, 116#u8, 87#u8, 105#u8, 116#u8, 104#u8]
/-- `owl:inverseOf` -/
def owlInverseOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 105#u8, 110#u8, 118#u8, 101#u8, 114#u8, 115#u8, 101#u8, 79#u8, 102#u8]
/-- `owl:sameAs` -/
def owlSameAs : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 115#u8, 97#u8, 109#u8, 101#u8, 65#u8, 115#u8]
/-- `owl:differentFrom` -/
def owlDifferentFrom : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 100#u8, 105#u8, 102#u8, 102#u8, 101#u8, 114#u8, 101#u8, 110#u8, 116#u8, 70#u8, 114#u8, 111#u8, 109#u8]
/-- `owl:hasKey` -/
def owlHasKey : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 104#u8, 97#u8, 115#u8, 75#u8, 101#u8, 121#u8]
/-- `owl:members` -/
def owlMembers : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 109#u8, 101#u8, 109#u8, 98#u8, 101#u8, 114#u8, 115#u8]
/-- `owl:AllDisjointClasses` -/
def owlAllDisjointClasses : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 65#u8, 108#u8, 108#u8, 68#u8, 105#u8, 115#u8, 106#u8, 111#u8, 105#u8, 110#u8, 116#u8, 67#u8, 108#u8, 97#u8, 115#u8, 115#u8, 101#u8, 115#u8]
/-- `owl:AllDisjointProperties` -/
def owlAllDisjointProperties : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 65#u8, 108#u8, 108#u8, 68#u8, 105#u8, 115#u8, 106#u8, 111#u8, 105#u8, 110#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 105#u8, 101#u8, 115#u8]
/-- `owl:AllDifferent` -/
def owlAllDifferent : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 65#u8, 108#u8, 108#u8, 68#u8, 105#u8, 102#u8, 102#u8, 101#u8, 114#u8, 101#u8, 110#u8, 116#u8]
/-- `owl:NegativePropertyAssertion` -/
def owlNegativePropertyAssertion : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 78#u8, 101#u8, 103#u8, 97#u8, 116#u8, 105#u8, 118#u8, 101#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8, 65#u8, 115#u8, 115#u8, 101#u8, 114#u8, 116#u8, 105#u8, 111#u8, 110#u8]
/-- `owl:sourceIndividual` -/
def owlSourceIndividual : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 115#u8, 111#u8, 117#u8, 114#u8, 99#u8, 101#u8, 73#u8, 110#u8, 100#u8, 105#u8, 118#u8, 105#u8, 100#u8, 117#u8, 97#u8, 108#u8]
/-- `owl:assertionProperty` -/
def owlAssertionProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 97#u8, 115#u8, 115#u8, 101#u8, 114#u8, 116#u8, 105#u8, 111#u8, 110#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:targetIndividual` -/
def owlTargetIndividual : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 116#u8, 97#u8, 114#u8, 103#u8, 101#u8, 116#u8, 73#u8, 110#u8, 100#u8, 105#u8, 118#u8, 105#u8, 100#u8, 117#u8, 97#u8, 108#u8]
/-- `owl:targetValue` -/
def owlTargetValue : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 116#u8, 97#u8, 114#u8, 103#u8, 101#u8, 116#u8, 86#u8, 97#u8, 108#u8, 117#u8, 101#u8]
/-- `owl:FunctionalProperty` -/
def owlFunctionalProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 70#u8, 117#u8, 110#u8, 99#u8, 116#u8, 105#u8, 111#u8, 110#u8, 97#u8, 108#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:InverseFunctionalProperty` -/
def owlInverseFunctionalProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 73#u8, 110#u8, 118#u8, 101#u8, 114#u8, 115#u8, 101#u8, 70#u8, 117#u8, 110#u8, 99#u8, 116#u8, 105#u8, 111#u8, 110#u8, 97#u8, 108#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:ReflexiveProperty` -/
def owlReflexiveProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 82#u8, 101#u8, 102#u8, 108#u8, 101#u8, 120#u8, 105#u8, 118#u8, 101#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:IrreflexiveProperty` -/
def owlIrreflexiveProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 73#u8, 114#u8, 114#u8, 101#u8, 102#u8, 108#u8, 101#u8, 120#u8, 105#u8, 118#u8, 101#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:SymmetricProperty` -/
def owlSymmetricProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 83#u8, 121#u8, 109#u8, 109#u8, 101#u8, 116#u8, 114#u8, 105#u8, 99#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:AsymmetricProperty` -/
def owlAsymmetricProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 65#u8, 115#u8, 121#u8, 109#u8, 109#u8, 101#u8, 116#u8, 114#u8, 105#u8, 99#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:TransitiveProperty` -/
def owlTransitiveProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 84#u8, 114#u8, 97#u8, 110#u8, 115#u8, 105#u8, 116#u8, 105#u8, 118#u8, 101#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:intersectionOf` -/
def owlIntersectionOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 105#u8, 110#u8, 116#u8, 101#u8, 114#u8, 115#u8, 101#u8, 99#u8, 116#u8, 105#u8, 111#u8, 110#u8, 79#u8, 102#u8]
/-- `owl:unionOf` -/
def owlUnionOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 117#u8, 110#u8, 105#u8, 111#u8, 110#u8, 79#u8, 102#u8]
/-- `owl:complementOf` -/
def owlComplementOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 99#u8, 111#u8, 109#u8, 112#u8, 108#u8, 101#u8, 109#u8, 101#u8, 110#u8, 116#u8, 79#u8, 102#u8]
/-- `owl:oneOf` -/
def owlOneOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 111#u8, 110#u8, 101#u8, 79#u8, 102#u8]
/-- `owl:onProperty` -/
def owlOnProperty : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 111#u8, 110#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]
/-- `owl:someValuesFrom` -/
def owlSomeValuesFrom : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 115#u8, 111#u8, 109#u8, 101#u8, 86#u8, 97#u8, 108#u8, 117#u8, 101#u8, 115#u8, 70#u8, 114#u8, 111#u8, 109#u8]
/-- `owl:allValuesFrom` -/
def owlAllValuesFrom : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 97#u8, 108#u8, 108#u8, 86#u8, 97#u8, 108#u8, 117#u8, 101#u8, 115#u8, 70#u8, 114#u8, 111#u8, 109#u8]
/-- `owl:hasValue` -/
def owlHasValue : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 104#u8, 97#u8, 115#u8, 86#u8, 97#u8, 108#u8, 117#u8, 101#u8]
/-- `owl:hasSelf` -/
def owlHasSelf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 104#u8, 97#u8, 115#u8, 83#u8, 101#u8, 108#u8, 102#u8]
/-- `owl:minCardinality` -/
def owlMinCardinality : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 109#u8, 105#u8, 110#u8, 67#u8, 97#u8, 114#u8, 100#u8, 105#u8, 110#u8, 97#u8, 108#u8, 105#u8, 116#u8, 121#u8]
/-- `owl:maxCardinality` -/
def owlMaxCardinality : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 109#u8, 97#u8, 120#u8, 67#u8, 97#u8, 114#u8, 100#u8, 105#u8, 110#u8, 97#u8, 108#u8, 105#u8, 116#u8, 121#u8]
/-- `owl:cardinality` -/
def owlCardinality : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 99#u8, 97#u8, 114#u8, 100#u8, 105#u8, 110#u8, 97#u8, 108#u8, 105#u8, 116#u8, 121#u8]
/-- `owl:minQualifiedCardinality` -/
def owlMinQualifiedCardinality : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 109#u8, 105#u8, 110#u8, 81#u8, 117#u8, 97#u8, 108#u8, 105#u8, 102#u8, 105#u8, 101#u8, 100#u8, 67#u8, 97#u8, 114#u8, 100#u8, 105#u8, 110#u8, 97#u8, 108#u8, 105#u8, 116#u8, 121#u8]
/-- `owl:maxQualifiedCardinality` -/
def owlMaxQualifiedCardinality : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 109#u8, 97#u8, 120#u8, 81#u8, 117#u8, 97#u8, 108#u8, 105#u8, 102#u8, 105#u8, 101#u8, 100#u8, 67#u8, 97#u8, 114#u8, 100#u8, 105#u8, 110#u8, 97#u8, 108#u8, 105#u8, 116#u8, 121#u8]
/-- `owl:qualifiedCardinality` -/
def owlQualifiedCardinality : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 113#u8, 117#u8, 97#u8, 108#u8, 105#u8, 102#u8, 105#u8, 101#u8, 100#u8, 67#u8, 97#u8, 114#u8, 100#u8, 105#u8, 110#u8, 97#u8, 108#u8, 105#u8, 116#u8, 121#u8]
/-- `owl:onClass` -/
def owlOnClass : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 111#u8, 110#u8, 67#u8, 108#u8, 97#u8, 115#u8, 115#u8]
/-- `owl:onDataRange` -/
def owlOnDataRange : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 111#u8, 110#u8, 68#u8, 97#u8, 116#u8, 97#u8, 82#u8, 97#u8, 110#u8, 103#u8, 101#u8]
/-- `owl:datatypeComplementOf` -/
def owlDatatypeComplementOf : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 100#u8, 97#u8, 116#u8, 97#u8, 116#u8, 121#u8, 112#u8, 101#u8, 67#u8, 111#u8, 109#u8, 112#u8, 108#u8, 101#u8, 109#u8, 101#u8, 110#u8, 116#u8, 79#u8, 102#u8]
/-- `owl:onDatatype` -/
def owlOnDatatype : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 111#u8, 110#u8, 68#u8, 97#u8, 116#u8, 97#u8, 116#u8, 121#u8, 112#u8, 101#u8]
/-- `owl:withRestrictions` -/
def owlWithRestrictions : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8, 55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 119#u8, 105#u8, 116#u8, 104#u8, 82#u8, 101#u8, 115#u8, 116#u8, 114#u8, 105#u8, 99#u8, 116#u8, 105#u8, 111#u8, 110#u8, 115#u8]
/-- `xsd:nonNegativeInteger` -/
def xsdNonNegativeInteger : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 110#u8, 111#u8, 110#u8, 78#u8, 101#u8, 103#u8, 97#u8, 116#u8, 105#u8, 118#u8, 101#u8, 73#u8, 110#u8, 116#u8, 101#u8, 103#u8, 101#u8, 114#u8]
/-- `xsd:boolean` -/
def xsdBoolean : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 98#u8, 111#u8, 111#u8, 108#u8, 101#u8, 97#u8, 110#u8]
/-- `xsd:string` -/
def xsdString : List U8 := [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8, 119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 49#u8, 47#u8, 88#u8, 77#u8, 76#u8, 83#u8, 99#u8, 104#u8, 101#u8, 109#u8, 97#u8, 35#u8, 115#u8, 116#u8, 114#u8, 105#u8, 110#u8, 103#u8]

/-! ### Views of RDF terms and the patterns the mapping produces -/

/-- The text of an RDF literal: a lexical form with a datatype IRI or a
    language tag. -/
inductive LiteralView
  | typed (lexical datatype : List U8)
  | tagged (lexical tag : List U8)
  deriving DecidableEq

/-- A node of a triple: an IRI by its spelling, a blank node, or a literal. -/
inductive Node
  | iri (spelling : List U8)
  | blank (node : rdf.BlankNode)
  | literal (view : LiteralView)

/-- A triple of the forward mapping, with its predicate by spelling. -/
structure Pattern where
  subject : Node
  predicate : List U8
  object : Node

def literalView (literal : rdf.RdfLiteral) : LiteralView :=
  match literal.kind with
  | .Datatype datatype => .typed literal.lexical.val datatype.spelling.val
  | .Language tag => .tagged literal.lexical.val tag.val

def subjectView : rdf.Subject → Node
  | .Iri iri => .iri iri.spelling.val
  | .Blank node => .blank node

def objectView : rdf.Object → Node
  | .Iri iri => .iri iri.spelling.val
  | .Blank node => .blank node
  | .Literal literal => .literal (literalView literal)

/-- A triple instantiates a pattern. -/
def Matches (pattern : Pattern) (triple : rdf.Triple) : Prop :=
  subjectView triple.subject = pattern.subject ∧ triple.predicate.spelling.val = pattern.predicate ∧
    objectView triple.object = pattern.object

/-! ### The forward mapping of names, individuals and literals -/

def iriNode (iri : model.Iri) : Node := .iri iri.spelling.val

def anonymousNode (individual : model.AnonymousIndividual) : Node :=
  .blank ⟨individual.scope, individual.label⟩

def individualNode : model.Individual → Node
  | .Named named => iriNode named.iri
  | .Anonymous anonymous => anonymousNode anonymous

/-- The RDF literal of a structural literal: an `rdf:PlainLiteral` with the
    language tag after its last `@`, or an `xsd:string` literal when the tag is
    empty; every other literal as it is. -/
inductive LiteralNode : model.Literal → Node → Prop
  | typed (literal : model.Literal) :
      literal.datatype.iri.spelling.val ≠ rdfPlainLiteral →
      LiteralNode literal (.literal (.typed literal.lexical.val literal.datatype.iri.spelling.val))
  | tagged (literal : model.Literal) (text tag : List U8) :
      literal.datatype.iri.spelling.val = rdfPlainLiteral → literal.lexical.val = text ++ 64#u8 :: tag →
      tag ≠ [] → 64#u8 ∉ tag →
      LiteralNode literal (.literal (.tagged text tag))
  | plain (literal : model.Literal) (text : List U8) :
      literal.datatype.iri.spelling.val = rdfPlainLiteral → literal.lexical.val = text ++ [64#u8] →
      LiteralNode literal (.literal (.typed text xsdString))

/-- The canonical decimal spelling of a number: digits without a leading zero,
    or the single digit `0`. -/
def Canonical (digits : List U8) (value : Nat) : Prop :=
  digits ≠ [] ∧ Rowl.Decimal.Digits digits ∧ Rowl.Decimal.Numeric digits 0 = value ∧
    (digits.length = 1 ∨ digits.head? ≠ some 48#u8)

/-- The `xsd:nonNegativeInteger` literal of a cardinality. -/
def NaturalNode (n : probes.Natural) (node : Node) : Prop :=
  ∃ digits, Canonical digits (Rowl.Probes.naturalValue n) ∧ node = .literal (.typed digits xsdNonNegativeInteger)

/-- `"true"^^xsd:boolean`. -/
def trueNode : Node := .literal (.typed [116#u8, 114#u8, 117#u8, 101#u8] xsdBoolean)

/-- The blank nodes the forward mapping allocates, in order. -/
abbrev Supply := List rdf.BlankNode

/-- The first node and the triples of an RDF list with these cells and
    elements. -/
def listOf : List rdf.BlankNode → List Node → Node × List Pattern
  | cell :: cells, element :: elements =>
    let (next, rest) := listOf cells elements
    (.blank cell, ⟨.blank cell, rdfFirst, element⟩ :: ⟨.blank cell, rdfRest, next⟩ :: rest)
  | _, _ => (.iri rdfNil, [])

/-- The members of a list of at least two, in order. -/
def members2 {α : Type} (xs : model.AtLeastTwo α) : List α := xs.first :: xs.second :: xs.rest.val

/-- The members of a nonempty list, in order. -/
def members1 {α : Type} (xs : model.NonEmpty α) : List α := xs.first :: xs.rest.val

/-! ### The forward mapping of expressions -/

/-- An object property expression: a property, or a fresh blank node for its
    inverse. -/
inductive TOPE : model.ObjectPropertyExpression → Supply → Node → List Pattern → Supply → Prop
  | named (property : model.ObjectProperty) (s : Supply) : TOPE (.Property property) s (iriNode property.iri) [] s
  | inverse (property : model.ObjectProperty) (x : rdf.BlankNode) (s : Supply) :
      TOPE (.Inverse property) (x :: s) (.blank x) [⟨.blank x, owlInverseOf, iriNode property.iri⟩] s

/-- Object property expressions in order. -/
inductive TOPEs : List model.ObjectPropertyExpression → Supply → List Node → List Pattern → Supply → Prop
  | nil (s : Supply) : TOPEs [] s [] [] s
  | cons (e : model.ObjectPropertyExpression) (es : List model.ObjectPropertyExpression) (s s1 s2 : Supply)
      (n : Node) (ns : List Node) (ps qs : List Pattern) :
      TOPE e s n ps s1 → TOPEs es s1 ns qs s2 → TOPEs (e :: es) s (n :: ns) (ps ++ qs) s2

/-- Facet restrictions in order: a fresh blank node each, with its facet and value. -/
inductive TFacets : List model.FacetRestriction → Supply → List Node → List Pattern → Supply → Prop
  | nil (s : Supply) : TFacets [] s [] [] s
  | cons (f : model.FacetRestriction) (fs : List model.FacetRestriction) (y : rdf.BlankNode) (s s' : Supply)
      (value : Node) (ns : List Node) (ps : List Pattern) :
      LiteralNode f.value value → TFacets fs s ns ps s' →
      TFacets (f :: fs) (y :: s) (.blank y :: ns) (⟨.blank y, f.facet.spelling.val, value⟩ :: ps) s'

mutual
/-- A data range (§2.1, Table 3). -/
inductive TDR : model.DataRange → Supply → Node → List Pattern → Supply → Prop
  | datatype (datatype : model.Datatype) (s : Supply) : TDR (.Datatype datatype) s (iriNode datatype.iri) [] s
  | intersection (xs : model.AtLeastTwo model.DataRange) (x : rdf.BlankNode) (cells : List rdf.BlankNode)
      (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      cells.length = (members2 xs).length → TDRs (members2 xs) s nodes ps s' →
      TDR (.Intersection xs) (x :: (cells ++ s)) (.blank x)
        (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlIntersectionOf, (listOf cells nodes).1⟩ ::
          ((listOf cells nodes).2 ++ ps)) s'
  | union (xs : model.AtLeastTwo model.DataRange) (x : rdf.BlankNode) (cells : List rdf.BlankNode)
      (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      cells.length = (members2 xs).length → TDRs (members2 xs) s nodes ps s' →
      TDR (.Union xs) (x :: (cells ++ s)) (.blank x)
        (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlUnionOf, (listOf cells nodes).1⟩ ::
          ((listOf cells nodes).2 ++ ps)) s'
  | complement (range : model.DataRange) (x : rdf.BlankNode) (s s' : Supply) (node : Node) (ps : List Pattern) :
      TDR range s node ps s' →
      TDR (.Complement range) (x :: s) (.blank x)
        (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlDatatypeComplementOf, node⟩ :: ps) s'
  | oneOf (xs : model.NonEmpty model.Literal) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s : Supply)
      (nodes : List Node) :
      cells.length = (members1 xs).length → List.Forall₂ LiteralNode (members1 xs) nodes →
      TDR (.OneOf xs) (x :: (cells ++ s)) (.blank x)
        (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlOneOf, (listOf cells nodes).1⟩ ::
          (listOf cells nodes).2) s
  | restriction (datatype : model.Datatype) (xs : model.NonEmpty model.FacetRestriction) (x : rdf.BlankNode)
      (cells : List rdf.BlankNode) (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      cells.length = (members1 xs).length → TFacets (members1 xs) s nodes ps s' →
      TDR (.Restriction datatype xs) (x :: (cells ++ s)) (.blank x)
        (⟨.blank x, rdfType, .iri rdfsDatatype⟩ :: ⟨.blank x, owlOnDatatype, iriNode datatype.iri⟩ ::
          ⟨.blank x, owlWithRestrictions, (listOf cells nodes).1⟩ :: ((listOf cells nodes).2 ++ ps)) s'

/-- Data ranges in order. -/
inductive TDRs : List model.DataRange → Supply → List Node → List Pattern → Supply → Prop
  | nil (s : Supply) : TDRs [] s [] [] s
  | cons (d : model.DataRange) (ds : List model.DataRange) (s s1 s2 : Supply) (n : Node) (ns : List Node)
      (ps qs : List Pattern) :
      TDR d s n ps s1 → TDRs ds s1 ns qs s2 → TDRs (d :: ds) s (n :: ns) (ps ++ qs) s2
end

/-- The triples of a restriction node on a property. -/
def restrictionHead (x : rdf.BlankNode) (property : Node) : List Pattern :=
  [⟨.blank x, rdfType, .iri owlRestriction⟩, ⟨.blank x, owlOnProperty, property⟩]

mutual
/-- A class expression (§2.1, Table 4). -/
inductive TCE : model.ClassExpression → Supply → Node → List Pattern → Supply → Prop
  | named (c : model.Class) (s : Supply) : TCE (.Class c) s (iriNode c.iri) [] s
  | intersection (xs : model.AtLeastTwo model.ClassExpression) (x : rdf.BlankNode) (cells : List rdf.BlankNode)
      (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      cells.length = (members2 xs).length → TCEs (members2 xs) s nodes ps s' →
      TCE (.ObjectIntersectionOf xs) (x :: (cells ++ s)) (.blank x)
        (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, owlIntersectionOf, (listOf cells nodes).1⟩ ::
          ((listOf cells nodes).2 ++ ps)) s'
  | union (xs : model.AtLeastTwo model.ClassExpression) (x : rdf.BlankNode) (cells : List rdf.BlankNode)
      (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      cells.length = (members2 xs).length → TCEs (members2 xs) s nodes ps s' →
      TCE (.ObjectUnionOf xs) (x :: (cells ++ s)) (.blank x)
        (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, owlUnionOf, (listOf cells nodes).1⟩ ::
          ((listOf cells nodes).2 ++ ps)) s'
  | complement (c : model.ClassExpression) (x : rdf.BlankNode) (s s' : Supply) (node : Node) (ps : List Pattern) :
      TCE c s node ps s' →
      TCE (.ObjectComplementOf c) (x :: s) (.blank x)
        (⟨.blank x, rdfType, .iri owlClass⟩ :: ⟨.blank x, owlComplementOf, node⟩ :: ps) s'
  | oneOf (xs : model.NonEmpty model.Individual) (x : rdf.BlankNode) (cells : List rdf.BlankNode) (s : Supply) :
      cells.length = (members1 xs).length →
      TCE (.ObjectOneOf xs) (x :: (cells ++ s)) (.blank x)
        (⟨.blank x, rdfType, .iri owlClass⟩ ::
          ⟨.blank x, owlOneOf, (listOf cells ((members1 xs).map individualNode)).1⟩ ::
          (listOf cells ((members1 xs).map individualNode)).2) s
  | some (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
      (n1 n2 : Node) (p1 p2 : List Pattern) :
      TOPE role s n1 p1 s1 → TCE c s1 n2 p2 s2 →
      TCE (.ObjectSomeValuesFrom role c) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlSomeValuesFrom, n2⟩ :: (p1 ++ p2)) s2
  | all (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (x : rdf.BlankNode) (s s1 s2 : Supply)
      (n1 n2 : Node) (p1 p2 : List Pattern) :
      TOPE role s n1 p1 s1 → TCE c s1 n2 p2 s2 →
      TCE (.ObjectAllValuesFrom role c) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlAllValuesFrom, n2⟩ :: (p1 ++ p2)) s2
  | hasValue (role : model.ObjectPropertyExpression) (a : model.Individual) (x : rdf.BlankNode) (s s1 : Supply)
      (n1 : Node) (p1 : List Pattern) :
      TOPE role s n1 p1 s1 →
      TCE (.ObjectHasValue role a) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlHasValue, individualNode a⟩ :: p1) s1
  | hasSelf (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply) (n1 : Node)
      (p1 : List Pattern) :
      TOPE role s n1 p1 s1 →
      TCE (.ObjectHasSelf role) (x :: s) (.blank x) (restrictionHead x n1 ++ ⟨.blank x, owlHasSelf, trueNode⟩ :: p1) s1
  | min (n : probes.Natural) (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply)
      (n1 m : Node) (p1 : List Pattern) :
      TOPE role s n1 p1 s1 → NaturalNode n m →
      TCE (.ObjectMinCardinality n role none) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlMinCardinality, m⟩ :: p1) s1
  | max (n : probes.Natural) (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply)
      (n1 m : Node) (p1 : List Pattern) :
      TOPE role s n1 p1 s1 → NaturalNode n m →
      TCE (.ObjectMaxCardinality n role none) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlMaxCardinality, m⟩ :: p1) s1
  | exact (n : probes.Natural) (role : model.ObjectPropertyExpression) (x : rdf.BlankNode) (s s1 : Supply)
      (n1 m : Node) (p1 : List Pattern) :
      TOPE role s n1 p1 s1 → NaturalNode n m →
      TCE (.ObjectExactCardinality n role none) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlCardinality, m⟩ :: p1) s1
  | minQualified (n : probes.Natural) (role : model.ObjectPropertyExpression) (c : model.ClassExpression)
      (x : rdf.BlankNode) (s s1 s2 : Supply) (n1 n2 m : Node) (p1 p2 : List Pattern) :
      TOPE role s n1 p1 s1 → NaturalNode n m → TCE c s1 n2 p2 s2 →
      TCE (.ObjectMinCardinality n role (some c)) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlMinQualifiedCardinality, m⟩ :: ⟨.blank x, owlOnClass, n2⟩ ::
          (p1 ++ p2)) s2
  | maxQualified (n : probes.Natural) (role : model.ObjectPropertyExpression) (c : model.ClassExpression)
      (x : rdf.BlankNode) (s s1 s2 : Supply) (n1 n2 m : Node) (p1 p2 : List Pattern) :
      TOPE role s n1 p1 s1 → NaturalNode n m → TCE c s1 n2 p2 s2 →
      TCE (.ObjectMaxCardinality n role (some c)) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlMaxQualifiedCardinality, m⟩ :: ⟨.blank x, owlOnClass, n2⟩ ::
          (p1 ++ p2)) s2
  | exactQualified (n : probes.Natural) (role : model.ObjectPropertyExpression) (c : model.ClassExpression)
      (x : rdf.BlankNode) (s s1 s2 : Supply) (n1 n2 m : Node) (p1 p2 : List Pattern) :
      TOPE role s n1 p1 s1 → NaturalNode n m → TCE c s1 n2 p2 s2 →
      TCE (.ObjectExactCardinality n role (some c)) (x :: s) (.blank x)
        (restrictionHead x n1 ++ ⟨.blank x, owlQualifiedCardinality, m⟩ :: ⟨.blank x, owlOnClass, n2⟩ ::
          (p1 ++ p2)) s2
  | dataSome (property : model.DataProperty) (range : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply)
      (n : Node) (p : List Pattern) :
      TDR range s n p s1 →
      TCE (.DataSomeValuesFrom property range) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ ⟨.blank x, owlSomeValuesFrom, n⟩ :: p) s1
  | dataAll (property : model.DataProperty) (range : model.DataRange) (x : rdf.BlankNode) (s s1 : Supply)
      (n : Node) (p : List Pattern) :
      TDR range s n p s1 →
      TCE (.DataAllValuesFrom property range) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ ⟨.blank x, owlAllValuesFrom, n⟩ :: p) s1
  | dataHasValue (property : model.DataProperty) (value : model.Literal) (x : rdf.BlankNode) (s : Supply)
      (n : Node) :
      LiteralNode value n →
      TCE (.DataHasValue property value) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ [⟨.blank x, owlHasValue, n⟩]) s
  | dataMin (n : probes.Natural) (property : model.DataProperty) (x : rdf.BlankNode) (s : Supply) (m : Node) :
      NaturalNode n m →
      TCE (.DataMinCardinality n property none) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ [⟨.blank x, owlMinCardinality, m⟩]) s
  | dataMax (n : probes.Natural) (property : model.DataProperty) (x : rdf.BlankNode) (s : Supply) (m : Node) :
      NaturalNode n m →
      TCE (.DataMaxCardinality n property none) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ [⟨.blank x, owlMaxCardinality, m⟩]) s
  | dataExact (n : probes.Natural) (property : model.DataProperty) (x : rdf.BlankNode) (s : Supply) (m : Node) :
      NaturalNode n m →
      TCE (.DataExactCardinality n property none) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ [⟨.blank x, owlCardinality, m⟩]) s
  | dataMinQualified (n : probes.Natural) (property : model.DataProperty) (range : model.DataRange)
      (x : rdf.BlankNode) (s s1 : Supply) (m r : Node) (p : List Pattern) :
      NaturalNode n m → TDR range s r p s1 →
      TCE (.DataMinCardinality n property (some range)) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ ⟨.blank x, owlMinQualifiedCardinality, m⟩ ::
          ⟨.blank x, owlOnDataRange, r⟩ :: p) s1
  | dataMaxQualified (n : probes.Natural) (property : model.DataProperty) (range : model.DataRange)
      (x : rdf.BlankNode) (s s1 : Supply) (m r : Node) (p : List Pattern) :
      NaturalNode n m → TDR range s r p s1 →
      TCE (.DataMaxCardinality n property (some range)) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ ⟨.blank x, owlMaxQualifiedCardinality, m⟩ ::
          ⟨.blank x, owlOnDataRange, r⟩ :: p) s1
  | dataExactQualified (n : probes.Natural) (property : model.DataProperty) (range : model.DataRange)
      (x : rdf.BlankNode) (s s1 : Supply) (m r : Node) (p : List Pattern) :
      NaturalNode n m → TDR range s r p s1 →
      TCE (.DataExactCardinality n property (some range)) (x :: s) (.blank x)
        (restrictionHead x (iriNode property.iri) ++ ⟨.blank x, owlQualifiedCardinality, m⟩ ::
          ⟨.blank x, owlOnDataRange, r⟩ :: p) s1

/-- Class expressions in order. -/
inductive TCEs : List model.ClassExpression → Supply → List Node → List Pattern → Supply → Prop
  | nil (s : Supply) : TCEs [] s [] [] s
  | cons (c : model.ClassExpression) (cs : List model.ClassExpression) (s s1 s2 : Supply) (n : Node)
      (ns : List Node) (ps qs : List Pattern) :
      TCE c s n ps s1 → TCEs cs s1 ns qs s2 → TCEs (c :: cs) s (n :: ns) (ps ++ qs) s2
end

/-! ### The forward mapping of axioms and ontologies -/

/-- The node and declaration type of an entity. -/
def declarationPattern : model.Entity → Pattern
  | .Class c => ⟨iriNode c.iri, rdfType, .iri owlClass⟩
  | .Datatype d => ⟨iriNode d.iri, rdfType, .iri rdfsDatatype⟩
  | .ObjectProperty p => ⟨iriNode p.iri, rdfType, .iri owlObjectProperty⟩
  | .DataProperty p => ⟨iriNode p.iri, rdfType, .iri owlDatatypeProperty⟩
  | .AnnotationProperty p => ⟨iriNode p.iri, rdfType, .iri owlAnnotationProperty⟩
  | .NamedIndividual a => ⟨iriNode a.iri, rdfType, .iri owlNamedIndividual⟩

/-- Consecutive members joined by a predicate: `n₁ p n₂`, `n₂ p n₃`, … -/
def chainOf (predicate : List U8) : List Node → List Pattern
  | n1 :: n2 :: rest => ⟨n1, predicate, n2⟩ :: chainOf predicate (n2 :: rest)
  | _ => []

def annotationSubjectNode : model.AnnotationSubject → Node
  | .Iri iri => iriNode iri
  | .Anonymous anonymous => anonymousNode anonymous

/-- The node of an annotation value. -/
inductive AnnotationValueNode : model.AnnotationValue → Node → Prop
  | iri (iri : model.Iri) : AnnotationValueNode (.Iri iri) (iriNode iri)
  | anonymous (anonymous : model.AnonymousIndividual) : AnnotationValueNode (.Anonymous anonymous) (anonymousNode anonymous)
  | literal (literal : model.Literal) (n : Node) : LiteralNode literal n → AnnotationValueNode (.Literal literal) n

/-- The type IRI of each object property characteristic. -/
def characteristicType : model.Axiom → Option (model.ObjectPropertyExpression × List U8)
  | .FunctionalObjectProperty role => some (role, owlFunctionalProperty)
  | .InverseFunctionalObjectProperty role => some (role, owlInverseFunctionalProperty)
  | .ReflexiveObjectProperty role => some (role, owlReflexiveProperty)
  | .IrreflexiveObjectProperty role => some (role, owlIrreflexiveProperty)
  | .SymmetricObjectProperty role => some (role, owlSymmetricProperty)
  | .AsymmetricObjectProperty role => some (role, owlAsymmetricProperty)
  | .TransitiveObjectProperty role => some (role, owlTransitiveProperty)
  | _ => none

/-- An axiom without annotations (§2.2, Table 1). -/
inductive TAxiom : model.Axiom → Supply → List Pattern → Supply → Prop
  | declaration (e : model.Entity) (s : Supply) : TAxiom (.Declaration e) s [declarationPattern e] s
  | subClassOf (c1 c2 : model.ClassExpression) (s s1 s2 : Supply) (n1 n2 : Node) (p1 p2 : List Pattern) :
      TCE c1 s n1 p1 s1 → TCE c2 s1 n2 p2 s2 →
      TAxiom (.SubClassOf c1 c2) s (⟨n1, rdfsSubClassOf, n2⟩ :: (p1 ++ p2)) s2
  | equivalentClasses (xs : model.AtLeastTwo model.ClassExpression) (s s' : Supply) (nodes : List Node)
      (ps : List Pattern) :
      TCEs (members2 xs) s nodes ps s' →
      TAxiom (.EquivalentClasses xs) s (chainOf owlEquivalentClass nodes ++ ps) s'
  | disjointClasses (c1 c2 : model.ClassExpression) (s s1 s2 : Supply) (n1 n2 : Node) (p1 p2 : List Pattern) :
      TCE c1 s n1 p1 s1 → TCE c2 s1 n2 p2 s2 →
      TAxiom (.DisjointClasses ⟨c1, c2, alloc.vec.Vec.new _⟩) s (⟨n1, owlDisjointWith, n2⟩ :: (p1 ++ p2)) s2
  | allDisjointClasses (xs : model.AtLeastTwo model.ClassExpression) (x : rdf.BlankNode)
      (cells : List rdf.BlankNode) (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      xs.rest.val ≠ [] → cells.length = (members2 xs).length → TCEs (members2 xs) s nodes ps s' →
      TAxiom (.DisjointClasses xs) (x :: (cells ++ s))
        (⟨.blank x, rdfType, .iri owlAllDisjointClasses⟩ :: ⟨.blank x, owlMembers, (listOf cells nodes).1⟩ ::
          ((listOf cells nodes).2 ++ ps)) s'
  | disjointUnion (c : model.Class) (xs : model.AtLeastTwo model.ClassExpression) (cells : List rdf.BlankNode)
      (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      cells.length = (members2 xs).length → TCEs (members2 xs) s nodes ps s' →
      TAxiom (.DisjointUnion c xs) (cells ++ s)
        (⟨iriNode c.iri, owlDisjointUnionOf, (listOf cells nodes).1⟩ :: ((listOf cells nodes).2 ++ ps)) s'
  | subObjectProperty (sub sup : model.ObjectPropertyExpression) (s s1 s2 : Supply) (n1 n2 : Node)
      (p1 p2 : List Pattern) :
      TOPE sub s n1 p1 s1 → TOPE sup s1 n2 p2 s2 →
      TAxiom (.SubObjectPropertyOf (.Single sub) sup) s (⟨n1, rdfsSubPropertyOf, n2⟩ :: (p1 ++ p2)) s2
  | propertyChain (chain : model.AtLeastTwo model.ObjectPropertyExpression) (sup : model.ObjectPropertyExpression)
      (cells : List rdf.BlankNode) (s s1 s2 : Supply) (n : Node) (nodes : List Node) (p ps : List Pattern) :
      TOPE sup s n p (cells ++ s1) → cells.length = (members2 chain).length → TOPEs (members2 chain) s1 nodes ps s2 →
      TAxiom (.SubObjectPropertyOf (.Chain chain) sup) s
        (⟨n, owlPropertyChainAxiom, (listOf cells nodes).1⟩ :: ((listOf cells nodes).2 ++ p ++ ps)) s2
  | equivalentObjectProperties (xs : model.AtLeastTwo model.ObjectPropertyExpression) (s s' : Supply)
      (nodes : List Node) (ps : List Pattern) :
      TOPEs (members2 xs) s nodes ps s' →
      TAxiom (.EquivalentObjectProperties xs) s (chainOf owlEquivalentProperty nodes ++ ps) s'
  | disjointObjectProperties (p1 p2 : model.ObjectPropertyExpression) (s s1 s2 : Supply) (n1 n2 : Node)
      (q1 q2 : List Pattern) :
      TOPE p1 s n1 q1 s1 → TOPE p2 s1 n2 q2 s2 →
      TAxiom (.DisjointObjectProperties ⟨p1, p2, alloc.vec.Vec.new _⟩) s (⟨n1, owlPropertyDisjointWith, n2⟩ :: (q1 ++ q2)) s2
  | allDisjointObjectProperties (xs : model.AtLeastTwo model.ObjectPropertyExpression) (x : rdf.BlankNode)
      (cells : List rdf.BlankNode) (s s' : Supply) (nodes : List Node) (ps : List Pattern) :
      xs.rest.val ≠ [] → cells.length = (members2 xs).length → TOPEs (members2 xs) s nodes ps s' →
      TAxiom (.DisjointObjectProperties xs) (x :: (cells ++ s))
        (⟨.blank x, rdfType, .iri owlAllDisjointProperties⟩ :: ⟨.blank x, owlMembers, (listOf cells nodes).1⟩ ::
          ((listOf cells nodes).2 ++ ps)) s'
  | inverseProperties (p1 p2 : model.ObjectPropertyExpression) (s s1 s2 : Supply) (n1 n2 : Node)
      (q1 q2 : List Pattern) :
      TOPE p1 s n1 q1 s1 → TOPE p2 s1 n2 q2 s2 →
      TAxiom (.InverseObjectProperties p1 p2) s (⟨n1, owlInverseOf, n2⟩ :: (q1 ++ q2)) s2
  | objectDomain (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (s s1 s2 : Supply)
      (n1 n2 : Node) (p1 p2 : List Pattern) :
      TOPE role s n1 p1 s1 → TCE c s1 n2 p2 s2 →
      TAxiom (.ObjectPropertyDomain role c) s (⟨n1, rdfsDomain, n2⟩ :: (p1 ++ p2)) s2
  | objectRange (role : model.ObjectPropertyExpression) (c : model.ClassExpression) (s s1 s2 : Supply)
      (n1 n2 : Node) (p1 p2 : List Pattern) :
      TOPE role s n1 p1 s1 → TCE c s1 n2 p2 s2 →
      TAxiom (.ObjectPropertyRange role c) s (⟨n1, rdfsRange, n2⟩ :: (p1 ++ p2)) s2
  | characteristic (a : model.Axiom) (role : model.ObjectPropertyExpression) (kind : List U8) (s s1 : Supply)
      (n : Node) (p : List Pattern) :
      characteristicType a = some (role, kind) → TOPE role s n p s1 →
      TAxiom a s (⟨n, rdfType, .iri kind⟩ :: p) s1
  | subDataProperty (d1 d2 : model.DataProperty) (s : Supply) :
      TAxiom (.SubDataPropertyOf d1 d2) s [⟨iriNode d1.iri, rdfsSubPropertyOf, iriNode d2.iri⟩] s
  | equivalentDataProperties (xs : model.AtLeastTwo model.DataProperty) (s : Supply) :
      TAxiom (.EquivalentDataProperties xs) s (chainOf owlEquivalentProperty ((members2 xs).map (iriNode ·.iri))) s
  | disjointDataProperties (d1 d2 : model.DataProperty) (s : Supply) :
      TAxiom (.DisjointDataProperties ⟨d1, d2, alloc.vec.Vec.new _⟩) s [⟨iriNode d1.iri, owlPropertyDisjointWith, iriNode d2.iri⟩] s
  | allDisjointDataProperties (xs : model.AtLeastTwo model.DataProperty) (x : rdf.BlankNode)
      (cells : List rdf.BlankNode) (s : Supply) :
      xs.rest.val ≠ [] → cells.length = (members2 xs).length →
      TAxiom (.DisjointDataProperties xs) (x :: (cells ++ s))
        (⟨.blank x, rdfType, .iri owlAllDisjointProperties⟩ ::
          ⟨.blank x, owlMembers, (listOf cells ((members2 xs).map (iriNode ·.iri))).1⟩ ::
          (listOf cells ((members2 xs).map (iriNode ·.iri))).2) s
  | dataDomain (d : model.DataProperty) (c : model.ClassExpression) (s s' : Supply) (n : Node) (p : List Pattern) :
      TCE c s n p s' → TAxiom (.DataPropertyDomain d c) s (⟨iriNode d.iri, rdfsDomain, n⟩ :: p) s'
  | dataRange (d : model.DataProperty) (r : model.DataRange) (s s' : Supply) (n : Node) (p : List Pattern) :
      TDR r s n p s' → TAxiom (.DataPropertyRange d r) s (⟨iriNode d.iri, rdfsRange, n⟩ :: p) s'
  | functionalData (d : model.DataProperty) (s : Supply) :
      TAxiom (.FunctionalDataProperty d) s [⟨iriNode d.iri, rdfType, .iri owlFunctionalProperty⟩] s
  | datatypeDefinition (d : model.Datatype) (r : model.DataRange) (s s' : Supply) (n : Node) (p : List Pattern) :
      TDR r s n p s' → TAxiom (.DatatypeDefinition d r) s (⟨iriNode d.iri, owlEquivalentClass, n⟩ :: p) s'
  | hasKey (c : model.ClassExpression) (objects : alloc.vec.Vec model.ObjectPropertyExpression)
      (datas : alloc.vec.Vec model.DataProperty) (cells : List rdf.BlankNode) (s s1 s2 : Supply) (n : Node)
      (nodes : List Node) (p ps : List Pattern) :
      TCE c s n p (cells ++ s1) → cells.length = objects.val.length + datas.val.length →
      TOPEs objects.val s1 nodes ps s2 →
      TAxiom (.HasKey c objects datas) s
        (⟨n, owlHasKey, (listOf cells (nodes ++ datas.val.map (iriNode ·.iri))).1⟩ ::
          ((listOf cells (nodes ++ datas.val.map (iriNode ·.iri))).2 ++ p ++ ps)) s2
  | sameIndividual (xs : model.AtLeastTwo model.Individual) (s : Supply) :
      TAxiom (.SameIndividual xs) s (chainOf owlSameAs ((members2 xs).map individualNode)) s
  | differentIndividuals (a b : model.Individual) (s : Supply) :
      TAxiom (.DifferentIndividuals ⟨a, b, alloc.vec.Vec.new _⟩) s [⟨individualNode a, owlDifferentFrom, individualNode b⟩] s
  | allDifferent (xs : model.AtLeastTwo model.Individual) (x : rdf.BlankNode) (cells : List rdf.BlankNode)
      (s : Supply) :
      xs.rest.val ≠ [] → cells.length = (members2 xs).length →
      TAxiom (.DifferentIndividuals xs) (x :: (cells ++ s))
        (⟨.blank x, rdfType, .iri owlAllDifferent⟩ ::
          ⟨.blank x, owlMembers, (listOf cells ((members2 xs).map individualNode)).1⟩ ::
          (listOf cells ((members2 xs).map individualNode)).2) s
  | classAssertion (c : model.ClassExpression) (a : model.Individual) (s s' : Supply) (n : Node) (p : List Pattern) :
      TCE c s n p s' → TAxiom (.ClassAssertion c a) s (⟨individualNode a, rdfType, n⟩ :: p) s'
  | objectAssertion (property : model.ObjectProperty) (a b : model.Individual) (s : Supply) :
      TAxiom (.ObjectPropertyAssertion (.Property property) a b) s
        [⟨individualNode a, property.iri.spelling.val, individualNode b⟩] s
  | inverseAssertion (property : model.ObjectProperty) (a b : model.Individual) (s : Supply) :
      TAxiom (.ObjectPropertyAssertion (.Inverse property) a b) s
        [⟨individualNode b, property.iri.spelling.val, individualNode a⟩] s
  | negativeObject (role : model.ObjectPropertyExpression) (a b : model.Individual) (x : rdf.BlankNode)
      (s s' : Supply) (n : Node) (p : List Pattern) :
      TOPE role s n p s' →
      TAxiom (.NegativeObjectPropertyAssertion role a b) (x :: s)
        (⟨.blank x, rdfType, .iri owlNegativePropertyAssertion⟩ :: ⟨.blank x, owlSourceIndividual, individualNode a⟩ ::
          ⟨.blank x, owlAssertionProperty, n⟩ :: ⟨.blank x, owlTargetIndividual, individualNode b⟩ :: p) s'
  | dataAssertion (d : model.DataProperty) (a : model.Individual) (value : model.Literal) (s : Supply) (n : Node) :
      LiteralNode value n →
      TAxiom (.DataPropertyAssertion d a value) s [⟨individualNode a, d.iri.spelling.val, n⟩] s
  | negativeData (d : model.DataProperty) (a : model.Individual) (value : model.Literal) (x : rdf.BlankNode)
      (s : Supply) (n : Node) :
      LiteralNode value n →
      TAxiom (.NegativeDataPropertyAssertion d a value) (x :: s)
        [⟨.blank x, rdfType, .iri owlNegativePropertyAssertion⟩, ⟨.blank x, owlSourceIndividual, individualNode a⟩,
          ⟨.blank x, owlAssertionProperty, iriNode d.iri⟩, ⟨.blank x, owlTargetValue, n⟩] s
  | annotationAssertion (property : model.AnnotationProperty) (subject : model.AnnotationSubject)
      (value : model.AnnotationValue) (s : Supply) (n : Node) :
      AnnotationValueNode value n →
      TAxiom (.AnnotationAssertion property subject value) s
        [⟨annotationSubjectNode subject, property.iri.spelling.val, n⟩] s
  | subAnnotationProperty (a1 a2 : model.AnnotationProperty) (s : Supply) :
      TAxiom (.SubAnnotationPropertyOf a1 a2) s [⟨iriNode a1.iri, rdfsSubPropertyOf, iriNode a2.iri⟩] s
  | annotationDomain (property : model.AnnotationProperty) (iri : model.Iri) (s : Supply) :
      TAxiom (.AnnotationPropertyDomain property iri) s [⟨iriNode property.iri, rdfsDomain, iriNode iri⟩] s
  | annotationRange (property : model.AnnotationProperty) (iri : model.Iri) (s : Supply) :
      TAxiom (.AnnotationPropertyRange property iri) s [⟨iriNode property.iri, rdfsRange, iriNode iri⟩] s

/-- Axioms without annotations, in order. -/
inductive TAxioms : List model.AnnotatedAxiom → Supply → List Pattern → Supply → Prop
  | nil (s : Supply) : TAxioms [] s [] s
  | cons (a : model.AnnotatedAxiom) (rest : List model.AnnotatedAxiom) (s s1 s2 : Supply) (p q : List Pattern) :
      a.annotations.val = [] → TAxiom a.axiom s p s1 → TAxioms rest s1 q s2 → TAxioms (a :: rest) s (p ++ q) s2

/-- An ontology annotation without annotations of its own. -/
inductive TAnnotation (ontology : Node) : model.Annotation → Pattern → Prop
  | mk (annotation : model.Annotation) (n : Node) :
      annotation.annotations.val = [] → AnnotationValueNode annotation.value n →
      TAnnotation ontology annotation ⟨ontology, annotation.property.iri.spelling.val, n⟩

/-- The ontology header (§2.2): the ontology IRI typed `owl:Ontology`, its
    version IRI, its imports and its annotations. An anonymous ontology without
    imports or annotations has no header triple. -/
inductive THeader : model.RawOntology → List Pattern → Prop
  | anonymous (o : model.RawOntology) :
      o.identity = .Anonymous → o.imports.val = [] → o.annotations.val = [] → THeader o []
  | named (o : model.RawOntology) (iri : model.Iri) (version : Option model.Iri) (annotations : List Pattern) :
      o.identity = .Named iri version → List.Forall₂ (TAnnotation (iriNode iri)) o.annotations.val annotations →
      THeader o (⟨iriNode iri, rdfType, .iri owlOntology⟩ ::
        ((match version with
          | some v => [⟨iriNode iri, owlVersionIRI, iriNode v⟩]
          | none => []) ++
          o.imports.val.map (fun i => ⟨iriNode iri, owlImports, iriNode i⟩) ++ annotations))

/-- The forward mapping of an ontology whose axioms carry no annotations, with
    exactly the blank nodes `supply`. -/
def TOntology (o : model.RawOntology) (supply : Supply) (patterns : List Pattern) : Prop :=
  ∃ header axioms, THeader o header ∧ TAxioms o.axioms.val supply axioms [] ∧ patterns = header ++ axioms

/-! ### Comparisons and lookups -/

attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

private theorem equal_from_correct (left : alloc.vec.Vec U8) (right : Slice U8)
    (equalLength : left.val.length = right.val.length) (index : Usize) :
    rdf_mapping.equal_from left right index = .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [rdf_mapping.equal_from]
  by_cases h : index.val < right.val.length
  · have hl : index.val < left.val.length := by omega
    have hlIndex : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hl]
    have hrIndex : right.index_usize index = .ok right.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem h]
    by_cases heads : left.val[index.val] = right.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := equal_from_correct left right equalLength next
      simp [UScalar.lt_equiv, h, hl, hlIndex, hrIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons h]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · simp [UScalar.lt_equiv, h, hl, hlIndex, hrIndex, heads]
      rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons h]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have hk : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, h, hk, hp]
termination_by right.val.length - index.val
decreasing_by omega

theorem same_correct (left : alloc.vec.Vec U8) (key : Slice U8) :
    rdf_mapping.same left key = .ok (decide (left.val = key.val)) := by
  rw [rdf_mapping.same]
  by_cases h : left.val.length = key.val.length
  · have ih := equal_from_correct left key h 0#usize
    simpa [h] using ih
  · have unequal : left.val ≠ key.val := fun eq => h (congrArg List.length eq)
    simp [h, unequal]

private theorem equal_vec_from_correct (left right : alloc.vec.Vec U8)
    (equalLength : left.val.length = right.val.length) (index : Usize) :
    rdf_mapping.equal_vec_from left right index =
      .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [rdf_mapping.equal_vec_from]
  by_cases h : index.val < right.val.length
  · have hl : index.val < left.val.length := by omega
    have hlIndex : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hl]
    have hrIndex : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    by_cases heads : left.val[index.val] = right.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := equal_vec_from_correct left right equalLength next
      simp [UScalar.lt_equiv, h, hl, hlIndex, hrIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons h]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · simp [UScalar.lt_equiv, h, hl, hlIndex, hrIndex, heads]
      rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons h]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have hk : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, h, hk, hp]
termination_by right.val.length - index.val
decreasing_by omega

theorem same_vec_correct (left right : alloc.vec.Vec U8) :
    rdf_mapping.same_vec left right = .ok (decide (left = right)) := by
  rw [rdf_mapping.same_vec]
  by_cases h : left.val.length = right.val.length
  · have ih := equal_vec_from_correct left right h 0#usize
    have iff : left = right ↔ left.val = right.val := alloc.vec.Vec.eq_iff left right
    simpa [h, iff] using ih
  · have unequal : left ≠ right := fun eq => h (by rw [eq])
    simp [h, unequal]

theorem same_blank_correct (left right : rdf.BlankNode) :
    rdf_mapping.same_blank left right = .ok (decide (left = right)) := by
  obtain ⟨s1, l1⟩ := left
  obtain ⟨s2, l2⟩ := right
  rw [rdf_mapping.same_blank]
  by_cases scope : s1 = s2
  · subst scope
    by_cases label : l1 = l2
    · subst label
      simp [same_vec_correct]
    · simp [same_vec_correct, label]
  · simp [same_vec_correct, scope]

theorem same_literal_correct (left right : rdf.RdfLiteral) :
    rdf_mapping.same_literal left right = .ok (decide (left = right)) := by
  obtain ⟨lex1, kind1⟩ := left
  obtain ⟨lex2, kind2⟩ := right
  rw [rdf_mapping.same_literal]
  by_cases lexical : lex1 = lex2
  · subst lexical
    cases kind1 with
    | Datatype a =>
      cases kind2 with
      | Datatype b =>
        obtain ⟨a⟩ := a
        obtain ⟨b⟩ := b
        by_cases same : a = b
        · subst same; simp [same_vec_correct]
        · simp [same_vec_correct, same]
      | Language _ => simp [same_vec_correct]
    | Language a =>
      cases kind2 with
      | Datatype _ => simp [same_vec_correct]
      | Language b =>
        by_cases same : a = b
        · subst same; simp [same_vec_correct]
        · simp [same_vec_correct, same]
  · simp [same_vec_correct, lexical]

theorem same_subject_correct (left right : rdf.Subject) :
    rdf_mapping.same_subject left right = .ok (decide (left = right)) := by
  rw [rdf_mapping.same_subject.eq_def]
  cases left with
  | Iri a =>
    cases right with
    | Iri b =>
      obtain ⟨a⟩ := a
      obtain ⟨b⟩ := b
      by_cases same : a = b
      · subst same; simp [same_vec_correct]
      · simp [same_vec_correct, same]
    | Blank _ => simp
  | Blank a =>
    cases right with
    | Iri _ => simp
    | Blank b =>
      by_cases same : a = b
      · subst same; simp [same_blank_correct]
      · simp [same_blank_correct, same]

theorem same_object_correct (left right : rdf.Object) :
    rdf_mapping.same_object left right = .ok (decide (left = right)) := by
  rw [rdf_mapping.same_object.eq_def]
  cases left with
  | Iri a =>
    cases right with
    | Iri b =>
      obtain ⟨a⟩ := a
      obtain ⟨b⟩ := b
      by_cases same : a = b
      · subst same; simp [same_vec_correct]
      · simp [same_vec_correct, same]
    | Blank _ => simp
    | Literal _ => simp
  | Blank a =>
    cases right with
    | Iri _ => simp
    | Blank b =>
      by_cases same : a = b
      · subst same; simp [same_blank_correct]
      · simp [same_blank_correct, same]
    | Literal _ => simp
  | Literal a =>
    cases right with
    | Iri _ => simp
    | Blank _ => simp
    | Literal b =>
      by_cases same : a = b
      · subst same; simp [same_literal_correct]
      · simp [same_literal_correct, same]

theorem same_triple_correct (left right : rdf.Triple) :
    rdf_mapping.same_triple left right = .ok (decide (left = right)) := by
  obtain ⟨s1, ⟨p1⟩, o1⟩ := left
  obtain ⟨s2, ⟨p2⟩, o2⟩ := right
  rw [rdf_mapping.same_triple]
  by_cases subject : s1 = s2
  · subst subject
    by_cases predicate : p1 = p2
    · subst predicate
      by_cases object : o1 = o2
      · subst object; simp [same_subject_correct, same_vec_correct, same_object_correct]
      · simp [same_subject_correct, same_vec_correct, same_object_correct, object]
    · simp [same_subject_correct, same_vec_correct, predicate]
  · simp [same_subject_correct, subject]

theorem copy_blank_identity (node : rdf.BlankNode) : rdf_mapping.copy_blank node = .ok node := by
  simp [rdf_mapping.copy_blank, Rowl.Nnf.copy_bytes_identity]

theorem iri_of_identity (spelling : alloc.vec.Vec U8) : rdf_mapping.iri_of spelling = .ok ⟨spelling⟩ := by
  simp [rdf_mapping.iri_of, Rowl.Nnf.copy_bytes_identity]

theorem subject_node_view (subject : rdf.Subject) :
    ∃ node, rdf_mapping.subject_node subject = .ok node ∧ objectView node = subjectView subject := by
  cases subject with
  | Iri iri =>
    exact ⟨.Iri ⟨iri.spelling⟩, by simp [rdf_mapping.subject_node, Rowl.Nnf.copy_bytes_identity],
      by simp [objectView, subjectView]⟩
  | Blank node =>
    exact ⟨.Blank node, by simp [rdf_mapping.subject_node, copy_blank_identity], by simp [objectView, subjectView]⟩

theorem is_used_correct (used : alloc.vec.Vec Bool) (index : Usize) :
    rdf_mapping.is_used used index = .ok (decide (used.val[index.val]? ≠ some false)) := by
  rw [rdf_mapping.is_used]
  by_cases inside : index.val < used.val.length
  · have lookup : used.index_usize index = .ok used.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    cases value : used.val[index.val] <;>
      simp [UScalar.lt_equiv, inside, lookup, value, List.getElem?_eq_getElem inside]
  · simp [UScalar.lt_equiv, inside, List.getElem?_eq_none (show used.val.length ≤ index.val by omega)]

theorem take_correct (state : rdf_mapping.State) (index : Usize) :
    rdf_mapping.take state index = .ok { state with used := state.used.set index true } := by
  rw [rdf_mapping.take]
  by_cases inside : index.val < state.used.val.length
  · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize,
      List.getElem?_eq_getElem inside]
  · have same : state.used.set index true = state.used := by
      apply (alloc.vec.Vec.eq_iff _ _).mpr
      simp [alloc.vec.Vec.set_val_eq, List.set_eq_of_length_le (show state.used.val.length ≤ index.val by omega)]
    simp [UScalar.lt_equiv, inside, same]

theorem record_correct (state state' : rdf_mapping.State) (node : rdf.BlankNode)
    (ran : rdf_mapping.record state node = .ok state') :
    state'.used = state.used ∧ state'.blanks.val = state.blanks.val ++ [node] := by
  rw [rdf_mapping.record, copy_blank_identity] at ran
  simp only [bind_ok, alloc.vec.Vec.push] at ran
  split at ran
  · simp only [bind_ok, Result.ok.injEq] at ran
    subst ran
    exact ⟨rfl, by simp⟩
  · simp at ran

theorem about_correct (triple : rdf.Triple) (node : rdf.BlankNode) :
    rdf_mapping.about triple node = .ok (decide (subjectView triple.subject = .blank node)) := by
  rw [rdf_mapping.about]
  cases subject : triple.subject with
  | Iri _ => simp [subjectView]
  | Blank b => simp [same_blank_correct, subjectView]

/-- An index the lookups return: a triple, not yet used. -/
def Unused (triples : List rdf.Triple) (used : List Bool) (index : Nat) (triple : rdf.Triple) : Prop :=
  triples[index]? = some triple ∧ used[index]? = some false

theorem find_spec (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (node : rdf.BlankNode)
    (key : Slice U8) (index found : Usize) (ran : rdf_mapping.find triples used node key index = .ok (some found)) :
    ∃ t, Unused triples.val used.val found.val t ∧ subjectView t.subject = .blank node ∧
      t.predicate.spelling.val = key.val := by
  rw [rdf_mapping.find] at ran
  by_cases more : index.val < triples.val.length
  · have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, about_correct, same_correct, advance] at ran
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      by_cases here : subjectView triples.val[index.val].subject = .blank node
      · simp only [here, decide_true, ↓reduceIte] at ran
        by_cases named : triples.val[index.val].predicate.spelling.val = key.val
        · simp only [named, decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at ran
          subst ran
          exact ⟨_, ⟨List.getElem?_eq_getElem more, isUsed⟩, here, named⟩
        · simp only [named, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
          exact find_spec triples used node key next found ran
      · simp only [here, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
        exact find_spec triples used node key next found ran
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at ran
      exact find_spec triples used node key next found ran
  · simp [UScalar.lt_equiv, more] at ran
termination_by triples.val.length - index.val
decreasing_by all_goals (have := nextValue; simp at this; omega)

theorem object_is_correct (object : rdf.Object) (key : Slice U8) :
    rdf_mapping.object_is object key = .ok (decide (objectView object = .iri key.val)) := by
  rw [rdf_mapping.object_is.eq_def]
  cases object with
  | Iri iri => simp [same_correct, objectView]
  | Blank _ => simp [objectView]
  | Literal _ => simp [objectView]

private theorem slice_val (n : Usize) (bytes : List U8) (h : bytes.length = n.val) :
    (Array.to_slice (Array.make n bytes h)).val = bytes := by
  simp [Array.to_slice, Array.make]

theorem find_type_spec (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (node : rdf.BlankNode)
    (key : Slice U8) (index found : Usize)
    (ran : rdf_mapping.find_type triples used node key index = .ok (some found)) :
    ∃ t, Unused triples.val used.val found.val t ∧ subjectView t.subject = .blank node ∧
      t.predicate.spelling.val = rdfType ∧ objectView t.object = .iri key.val := by
  rw [rdf_mapping.find_type] at ran
  by_cases more : index.val < triples.val.length
  · have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, about_correct, same_correct, object_is_correct, advance, lift,
      slice_val] at ran
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      by_cases here : subjectView triples.val[index.val].subject = .blank node
      · simp only [here, decide_true, ↓reduceIte] at ran
        by_cases typed : triples.val[index.val].predicate.spelling.val = rdfType
        · simp only [rdfType] at typed
          simp only [typed, decide_true, ↓reduceIte] at ran
          by_cases object : objectView triples.val[index.val].object = .iri key.val
          · simp only [object, decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at ran
            subst ran
            exact ⟨_, ⟨List.getElem?_eq_getElem more, isUsed⟩, here, by simpa [rdfType] using typed, object⟩
          · simp only [object, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
            exact find_type_spec triples used node key next found ran
        · simp only [rdfType] at typed
          simp only [typed, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
          exact find_type_spec triples used node key next found ran
      · simp only [here, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
        exact find_type_spec triples used node key next found ran
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at ran
      exact find_type_spec triples used node key next found ran
  · simp [UScalar.lt_equiv, more] at ran
termination_by triples.val.length - index.val
decreasing_by all_goals (have := nextValue; simp at this; omega)

theorem find_any_spec (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (node : rdf.BlankNode)
    (index found : Usize) (ran : rdf_mapping.find_any triples used node index = .ok (some found)) :
    ∃ t, Unused triples.val used.val found.val t ∧ subjectView t.subject = .blank node := by
  rw [rdf_mapping.find_any] at ran
  by_cases more : index.val < triples.val.length
  · have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, about_correct, advance] at ran
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      by_cases here : subjectView triples.val[index.val].subject = .blank node
      · simp only [here, decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at ran
        subst ran
        exact ⟨_, ⟨List.getElem?_eq_getElem more, isUsed⟩, here⟩
      · simp only [here, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
        exact find_any_spec triples used node next found ran
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at ran
      exact find_any_spec triples used node next found ran
  · simp [UScalar.lt_equiv, more] at ran
termination_by triples.val.length - index.val
decreasing_by all_goals (have := nextValue; simp at this; omega)

theorem is_nil_correct (node : rdf.Object) :
    rdf_mapping.is_nil node = .ok (decide (objectView node = .iri rdfNil)) := by
  simp [rdf_mapping.is_nil, object_is_correct, lift, slice_val, rdfNil]

/-! ### Growth of the used triples -/

/-- From `s` to `s'`: the used flags only grow, the blank nodes `fresh` are
    appended, and the newly used triples are exactly the instances of
    `patterns`. -/
structure Grows (triples : List rdf.Triple) (s s' : rdf_mapping.State) (patterns : List Pattern)
    (fresh : List rdf.BlankNode) : Prop where
  length : s'.used.val.length = s.used.val.length
  keeps : ∀ (i : Nat), s.used.val[i]? = some true → s'.used.val[i]? = some true
  blanks : s'.blanks.val = s.blanks.val ++ fresh
  sound : ∀ (i : Nat), s.used.val[i]? = some false → s'.used.val[i]? = some true →
    ∃ t, triples[i]? = some t ∧ ∃ p ∈ patterns, Matches p t
  complete : ∀ p ∈ patterns, ∃ (i : Nat) (t : rdf.Triple), s.used.val[i]? = some false ∧ s'.used.val[i]? = some true ∧
    triples[i]? = some t ∧ Matches p t

theorem grows_refl (triples : List rdf.Triple) (s : rdf_mapping.State) : Grows triples s s [] [] where
  length := rfl
  keeps := fun _ h => h
  blanks := by simp
  sound := by
    intro i before after
    rw [before] at after
    cases after
  complete := by simp

theorem grows_trans {triples : List rdf.Triple} {s s1 s2 : rdf_mapping.State} {p1 p2 : List Pattern}
    {f1 f2 : List rdf.BlankNode} (first : Grows triples s s1 p1 f1) (second : Grows triples s1 s2 p2 f2) :
    Grows triples s s2 (p1 ++ p2) (f1 ++ f2) where
  length := by rw [second.length, first.length]
  keeps := fun i h => second.keeps i (first.keeps i h)
  blanks := by rw [second.blanks, first.blanks, List.append_assoc]
  sound := by
    intro i before after
    have inside : i < s.used.val.length := (List.getElem?_eq_some_iff.mp before).1
    have inside1 : i < s1.used.val.length := by rw [first.length]; exact inside
    cases middle : s1.used.val[i]'inside1 with
    | true =>
      have at1 : s1.used.val[i]? = some true := by rw [List.getElem?_eq_getElem inside1, middle]
      obtain ⟨t, at_t, p, member, fits⟩ := first.sound i before at1
      exact ⟨t, at_t, p, List.mem_append_left _ member, fits⟩
    | false =>
      have at1 : s1.used.val[i]? = some false := by rw [List.getElem?_eq_getElem inside1, middle]
      obtain ⟨t, at_t, p, member, fits⟩ := second.sound i at1 after
      exact ⟨t, at_t, p, List.mem_append_right _ member, fits⟩
  complete := by
    intro p member
    rcases List.mem_append.mp member with left | right
    · obtain ⟨i, t, before, after, at_t, fits⟩ := first.complete p left
      exact ⟨i, t, before, second.keeps i after, at_t, fits⟩
    · obtain ⟨i, t, before, after, at_t, fits⟩ := second.complete p right
      have inside1 : i < s1.used.val.length := (List.getElem?_eq_some_iff.mp before).1
      have inside : i < s.used.val.length := by rw [← first.length]; exact inside1
      cases earlier : s.used.val[i]'inside with
      | false => exact ⟨i, t, by rw [List.getElem?_eq_getElem inside, earlier], after, at_t, fits⟩
      | true =>
        have kept := first.keeps i (by rw [List.getElem?_eq_getElem inside, earlier])
        rw [before] at kept
        cases kept

/-- The same growth for patterns with the same members. -/
theorem grows_same {triples : List rdf.Triple} {s s' : rdf_mapping.State} {p q : List Pattern}
    {fresh : List rdf.BlankNode} (grows : Grows triples s s' p fresh) (same : ∀ x, x ∈ p ↔ x ∈ q) :
    Grows triples s s' q fresh where
  length := grows.length
  keeps := grows.keeps
  blanks := grows.blanks
  sound := by
    intro i before after
    obtain ⟨t, at_t, x, member, fits⟩ := grows.sound i before after
    exact ⟨t, at_t, x, (same x).mp member, fits⟩
  complete := fun x member => grows.complete x ((same x).mpr member)

theorem grows_take (triples : List rdf.Triple) (s : rdf_mapping.State) (index : Usize) (t : rdf.Triple)
    (p : Pattern) (unused : Unused triples s.used.val index.val t) (fits : Matches p t) :
    Grows triples s { s with used := s.used.set index true } [p] [] where
  length := by simp [alloc.vec.Vec.set_val_eq]
  keeps := by
    intro i h
    simp only [alloc.vec.Vec.set_val_eq]
    by_cases same : i = index.val
    · subst same
      rw [unused.2] at h
      cases h
    · rw [List.getElem?_set_ne (Ne.symm same)]
      exact h
  blanks := by simp
  sound := by
    intro i before after
    simp only [alloc.vec.Vec.set_val_eq] at after
    by_cases same : i = index.val
    · subst same
      exact ⟨t, unused.1, p, by simp, fits⟩
    · rw [List.getElem?_set_ne (Ne.symm same), before] at after
      cases after
  complete := by
    intro x member
    simp only [List.mem_singleton] at member
    subst member
    have inside : index.val < s.used.val.length := (List.getElem?_eq_some_iff.mp unused.2).1
    exact ⟨index.val, t, unused.2, by simp [alloc.vec.Vec.set_val_eq, List.getElem?_set_self inside], unused.1,
      fits⟩

theorem grows_record (triples : List rdf.Triple) (s s' : rdf_mapping.State) (node : rdf.BlankNode)
    (ran : rdf_mapping.record s node = .ok s') : Grows triples s s' [] [node] := by
  obtain ⟨used, blanks⟩ := record_correct s s' node ran
  exact {
    length := by rw [used]
    keeps := fun i h => by rw [used]; exact h
    blanks := blanks
    sound := by
      intro i before after
      rw [used, before] at after
      cases after
    complete := by simp }

/-- The triple a lookup found, used, as an instance of the pattern. -/
theorem take_grows (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (index : Usize) (t : rdf.Triple)
    (p : Pattern) (unused : Unused triples.val s.used.val index.val t) (fits : Matches p t) :
    ∃ s', rdf_mapping.take s index = .ok s' ∧ Grows triples.val s s' [p] [] :=
  ⟨_, take_correct s index, grows_take triples.val s index t p unused fits⟩

/-! ### Stepping through the Rust code -/

theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]

theorem bind_eq_ok {α β : Type} {x : Result α} {f : α → Result β} {y : β} (h : (x >>= f) = Result.ok y) :
    ∃ a, x = Result.ok a ∧ f a = Result.ok y := by
  cases hx : x.match with
  | ok a =>
    have xa : x = Result.ok a := Result.match.isOk.mp hx
    subst xa
    exact ⟨a, rfl, by simpa using h⟩
  | vis e k =>
    have xv : x = Result.vis e k := Result.match.isVis.mp hx
    subst xv
    have h' : Aeneas.Std.bind (Result.vis e k) f = Result.ok y := h
    rw [bind_vis] at h'
    exact absurd h' vis_not_ok
  | div =>
    have xd : x = Result.div := Result.match.isDiv.mp hx
    subst xd
    have h' : Aeneas.Std.bind Result.div f = Result.ok y := h
    rw [bind_div] at h'
    exact absurd h' div_not_ok

/-- The node of the element of the list cell whose `rdf:first` triple is at `k`. -/
def elementNode (triples : List rdf.Triple) (k : Usize) : Node :=
  match triples[k.val]? with
  | some t => objectView t.object
  | none => .iri []

theorem cell_spec (triples : alloc.vec.Vec rdf.Triple) (node : rdf.Object) (s s' : rdf_mapping.State)
    (first rest : Usize) (ran : rdf_mapping.cell triples node s = .ok (some (first, rest, s'))) :
    ∃ c tf tr, objectView node = .blank c ∧ triples.val[first.val]? = some tf ∧ triples.val[rest.val]? = some tr ∧
      Grows triples.val s s' [⟨.blank c, rdfFirst, objectView tf.object⟩, ⟨.blank c, rdfRest, objectView tr.object⟩]
        [c] := by
  rw [rdf_mapping.cell.eq_def] at ran
  cases node with
  | Iri _ => simp at ran
  | Literal _ => simp at ran
  | Blank c =>
    simp only [lift, bind_ok, take_correct] at ran
    obtain ⟨o, ho, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some f =>
      simp only at ran
      obtain ⟨o1, ho1, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some r =>
        simp only at ran
        obtain ⟨s3, hrec, ran⟩ := bind_eq_ok ran
        simp only [Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
        obtain ⟨rfl, rfl, rfl⟩ := ran
        obtain ⟨tf, unusedF, subjF, predF⟩ := find_spec _ _ _ _ _ _ ho
        obtain ⟨tr, unusedR, subjR, predR⟩ := find_spec _ _ _ _ _ _ ho1
        refine ⟨c, tf, tr, rfl, unusedF.1, unusedR.1, ?_⟩
        have g1 := grows_take triples.val s f tf ⟨.blank c, rdfFirst, objectView tf.object⟩ unusedF
          ⟨subjF, by simpa [slice_val, rdfFirst] using predF, rfl⟩
        have g2 := grows_take triples.val { s with used := s.used.set f true } r tr
          ⟨.blank c, rdfRest, objectView tr.object⟩ unusedR ⟨subjR, by simpa [slice_val, rdfRest] using predR, rfl⟩
        have g3 := grows_record triples.val _ s3 c hrec
        simpa using grows_trans (grows_trans g1 g2) g3

theorem cells_spec (triples : alloc.vec.Vec rdf.Triple) (fuel : Nat) :
    ∀ (f : Usize) (node : rdf.Object) (s s' : rdf_mapping.State) (out firsts : alloc.vec.Vec Usize),
      f.val = fuel → rdf_mapping.cells triples node s out f = .ok (some (firsts, s')) →
      ∃ news cells, firsts.val = out.val ++ news ∧ cells.length = news.length ∧
        Grows triples.val s s' (listOf cells (news.map (elementNode triples.val))).2 cells ∧
        (listOf cells (news.map (elementNode triples.val))).1 = objectView node := by
  induction fuel with
  | zero =>
    intro f node s s' out firsts same ran
    rw [rdf_mapping.cells] at ran
    simp only [is_nil_correct, bind_ok] at ran
    by_cases nil : objectView node = .iri rdfNil
    · simp only [nil, decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨[], [], by simp, rfl, grows_refl _ _, by simp [listOf, nil]⟩
    · have zero : ¬ f > 0#usize := by scalar_tac
      simp [nil, zero] at ran
  | succ n ih =>
    intro f node s s' out firsts same ran
    rw [rdf_mapping.cells] at ran
    simp only [is_nil_correct, bind_ok] at ran
    by_cases nil : objectView node = .iri rdfNil
    · simp only [nil, decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨[], [], by simp, rfl, grows_refl _ _, by simp [listOf, nil]⟩
    · have positive : f > 0#usize := by scalar_tac
      simp only [nil, decide_false, Bool.false_eq_true, ↓reduceIte, positive] at ran
      obtain ⟨o, ho, ran⟩ := bind_eq_ok ran
      cases o with
      | none => simp at ran
      | some t =>
        obtain ⟨first, rest, s1⟩ := t
        dsimp only at ran
        obtain ⟨c, tf, tr, view, atF, atR, grows⟩ := cell_spec triples node s s1 first rest ho
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out first room)
          have restIn : rest.val < triples.val.length := (List.getElem?_eq_some_iff.mp atR).1
          have lookup : triples.index_usize rest = .ok tr := by
            simp [alloc.vec.Vec.index_usize, atR]
          obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
            (Usize.sub_spec (x := f) (y := 1#usize) (by scalar_tac))
          have fewerIs : fewer.val = n := by simp at fewerValue; omega
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, lookup, back] at ran
          obtain ⟨news, cells, split, lengths, grows', head⟩ := ih fewer tr.object s1 s' pushed firsts fewerIs ran
          refine ⟨first :: news, c :: cells, by rw [split, contents]; simp, by simp [lengths], ?_, ?_⟩
          · have element : elementNode triples.val first = objectView tf.object := by simp [elementNode, atF]
            have combined := grows_trans grows grows'
            refine grows_same (by simpa using combined) ?_
            intro x
            simp only [List.map_cons, listOf, element, head, List.mem_cons, List.mem_append, List.mem_singleton]
          · simp [listOf, view]
        · have full : ¬ out.val.length < Usize.max := room
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, full] at ran

theorem element_spec (triples : alloc.vec.Vec rdf.Triple) (first : Usize) (node : rdf.Object)
    (ran : rdf_mapping.element triples first = .ok (some node)) : objectView node = elementNode triples.val first := by
  rw [rdf_mapping.element] at ran
  by_cases inside : first.val < triples.val.length
  · have lookup : triples.index_usize first = .ok triples.val[first.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
      bind_ok, Result.ok.injEq, Option.some.injEq] at ran
    subst ran
    simp [elementNode, List.getElem?_eq_getElem inside]
  · simp [UScalar.lt_equiv, inside] at ran

/-! ### Literals, numbers and individuals -/

theorem has_at_correct (bytes : alloc.vec.Vec U8) (index : Usize) :
    rdf_mapping.has_at bytes index = .ok (decide (64#u8 ∈ bytes.val.drop index.val)) := by
  rw [rdf_mapping.has_at]
  by_cases more : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    rw [List.drop_eq_getElem_cons more]
    by_cases here : bytes.val[index.val] = 64#u8
    · simp [UScalar.lt_equiv, more, lookup, here]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := has_at_correct bytes next
      rw [nextIndex] at rest
      have other : (64#u8 ∈ bytes.val[index.val] :: bytes.val.drop (index.val + 1)) ↔
          64#u8 ∈ bytes.val.drop (index.val + 1) := by
        rw [List.mem_cons]
        exact ⟨fun h => h.resolve_left (fun same => here same.symm), Or.inr⟩
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup,
        bind_ok, here, advance, rest, other]
  · have empty : bytes.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, more, empty]
termination_by bytes.val.length - index.val
decreasing_by omega

theorem append_from_spec (bytes : alloc.vec.Vec U8) :
    ∀ (index : Usize) (out result : alloc.vec.Vec U8),
      out.val.length + (bytes.val.length - index.val) ≤ Usize.max →
      rdf_mapping.append_from out bytes index = .ok result → result.val = out.val ++ bytes.val.drop index.val := by
  intro index
  induction h : bytes.val.length - index.val generalizing index with
  | zero =>
    intro out result _ ran
    rw [rdf_mapping.append_from] at ran
    have done : ¬ index.val < bytes.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    simp [List.drop_eq_nil_iff.mpr (show bytes.val.length ≤ index.val by omega)]
  | succ n ih =>
    intro out result room ran
    rw [rdf_mapping.append_from] at ran
    have more : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out bytes.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, usize_max_val, fits,
      alloc.vec.Vec.index_slice_index, lookup, bind_ok, push, advance] at ran
    have result' := ih next (by omega) pushed result (by rw [contents]; simp; omega) ran
    rw [result', contents, nextIndex, List.drop_eq_getElem_cons more]
    simp

theorem spelled_spec (key : Slice U8) :
    ∀ (index : Usize) (out result : alloc.vec.Vec U8), out.val.length ≤ index.val →
      rdf_mapping.spelled key index out = .ok result → result.val = out.val ++ key.val.drop index.val := by
  intro index
  induction h : key.val.length - index.val generalizing index with
  | zero =>
    intro out result _ ran
    rw [rdf_mapping.spelled] at ran
    have done : ¬ index.val < key.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    simp [List.drop_eq_nil_iff.mpr (show key.val.length ≤ index.val by omega)]
  | succ n ih =>
    intro out result small ran
    rw [rdf_mapping.spelled] at ran
    have more : index.val < key.val.length := by omega
    have lookup : key.index_usize index = .ok key.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem more]
    have fits : out.val.length < Usize.max := by have := key.property; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out key.val[index.val] fits)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    simp only [Slice.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.len_val, usize_max_val, fits,
      lookup, bind_ok, push, advance] at ran
    have result' := ih next (by omega) pushed result (by rw [contents]; simp; omega) ran
    rw [result', contents, nextIndex, List.drop_eq_getElem_cons more]
    simp

theorem literal_of_spec (literal : rdf.RdfLiteral) (value : model.Literal)
    (ran : rdf_mapping.literal_of literal = .ok (some value)) :
    LiteralNode value (.literal (literalView literal)) := by
  obtain ⟨lexical, kind⟩ := literal
  rw [rdf_mapping.literal_of] at ran
  cases kind with
  | Datatype datatype =>
    simp only [lift, bind_ok, same_correct, slice_val] at ran
    by_cases plain : datatype.spelling.val = rdfPlainLiteral
    · simp only [rdfPlainLiteral] at plain
      simp [plain] at ran
    · simp only [rdfPlainLiteral] at plain
      simp only [plain, decide_false, Bool.false_eq_true, ↓reduceIte, Rowl.Nnf.copy_bytes_identity, iri_of_identity,
        bind_ok, Result.ok.injEq, Option.some.injEq] at ran
      subst ran
      exact LiteralNode.typed _ (by simpa [rdfPlainLiteral] using plain)
  | Language tag =>
    simp only at ran
    by_cases empty : tag.val.length = 0
    · have zero : alloc.vec.Vec.len tag = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [empty]
      simp [zero] at ran
    · have nonzero : ¬ alloc.vec.Vec.len tag = 0#usize := by
        intro same; apply empty; simpa using congrArg UScalar.val same
      simp only [nonzero, ↓reduceIte, has_at_correct, bind_ok] at ran
      by_cases at_sign : 64#u8 ∈ tag.val
      · simp [at_sign] at ran
      · simp only [show (0#usize).val = 0 from rfl, List.drop_zero, at_sign, decide_false, Bool.false_eq_true,
          ↓reduceIte] at ran
        obtain ⟨limit, limitRun, limitValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := core.num.Usize.MAX) (y := alloc.vec.Vec.len tag) (by scalar_tac))
        simp only [limitRun, bind_ok] at ran
        by_cases short : lexical.val.length < limit.val
        · have shortU : alloc.vec.Vec.len lexical < limit := by simpa [UScalar.lt_equiv] using short
          simp only [shortU, ↓reduceIte, Rowl.Nnf.copy_bytes_identity, bind_ok] at ran
          have fits : lexical.val.length < Usize.max := by
            have := limitValue; simp [usize_max_val] at this; omega
          obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec lexical 64#u8 fits)
          simp only [push, bind_ok, lift] at ran
          obtain ⟨appended, appendRun, ran⟩ := bind_eq_ok ran
          obtain ⟨spelling, spellRun, ran⟩ := bind_eq_ok ran
          simp only [Result.ok.injEq, Option.some.injEq] at ran
          subst ran
          have appendedIs := append_from_spec tag 0#usize pushed appended
            (by rw [contents]; have := limitValue; simp [usize_max_val] at this ⊢; omega) appendRun
          have spellingIs := spelled_spec _ 0#usize (alloc.vec.Vec.new U8) spelling (by simp) spellRun
          simp only [contents, show (0#usize).val = 0 from rfl, List.drop_zero] at appendedIs
          simp only [alloc.vec.Vec.new, List.nil_append, show (0#usize).val = 0 from rfl, List.drop_zero,
            slice_val] at spellingIs
          refine LiteralNode.tagged _ lexical.val tag.val (by simpa [rdfPlainLiteral] using spellingIs)
            (by simpa using appendedIs) (fun h => empty (by simp [h])) at_sign
        · have longU : ¬ alloc.vec.Vec.len lexical < limit := by simpa [UScalar.lt_equiv] using short
          simp [longU] at ran

theorem node_literal_spec (node : rdf.Object) (value : model.Literal)
    (ran : rdf_mapping.node_literal node = .ok (some value)) : LiteralNode value (objectView node) := by
  rw [rdf_mapping.node_literal.eq_def] at ran
  cases node with
  | Iri _ => simp at ran
  | Blank _ => simp at ran
  | Literal literal => exact literal_of_spec literal value ran

theorem natural_up_spec (count : Usize) (out result : probes.Natural)
    (ran : rdf_mapping.natural_up count out = .ok result) :
    Rowl.Probes.naturalValue result = count.val + Rowl.Probes.naturalValue out := by
  rw [rdf_mapping.natural_up] at ran
  by_cases zero : count = 0#usize
  · subst zero
    simp at ran
    subst ran
    simp
  · have positive : 0 < count.val := by
      have : count.val ≠ 0 := fun h => zero (UScalar.eq_of_val_eq (by simp [h]))
      omega
    obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := count) (y := 1#usize) (by scalar_tac))
    have fewerIs : fewer.val = count.val - 1 := by simp at fewerValue; omega
    simp only [zero, ↓reduceIte, back, bind_ok] at ran
    have inner := natural_up_spec fewer (.Succ out) result ran
    rw [inner, fewerIs]
    simp [Rowl.Probes.naturalValue]
    omega
termination_by count.val
decreasing_by
  have := fewerValue
  simp at this
  omega

private theorem canonical_of_bounded (lexical : alloc.vec.Vec U8) (value : Nat)
    (bounded : Rowl.Decimal.Bounded lexical.val 0 lexical.val.length 10000 value)
    (leading : 1 < lexical.val.length → lexical.val[0]? ≠ some 48#u8) :
    Canonical lexical.val value := by
  obtain ⟨positive, _, digits, numeric, _⟩ := bounded
  simp only [Rowl.Decimal.Slice, List.take_length, List.drop_zero] at digits numeric
  refine ⟨fun h => by simp [h] at positive, digits, numeric, ?_⟩
  by_cases one : lexical.val.length = 1
  · exact .inl one
  · refine .inr ?_
    have more : 1 < lexical.val.length := by omega
    have := leading more
    rwa [List.head?_eq_getElem?]

theorem node_natural_spec (node : rdf.Object) (n : probes.Natural)
    (ran : rdf_mapping.node_natural node = .ok (some n)) : NaturalNode n (objectView node) := by
  rw [rdf_mapping.node_natural.eq_def] at ran
  cases node with
  | Iri _ => simp at ran
  | Blank _ => simp at ran
  | Literal literal =>
    obtain ⟨lexical, kind⟩ := literal
    cases kind with
    | Language _ => simp at ran
    | Datatype datatype =>
      simp only [lift, bind_ok, same_correct, slice_val] at ran
      by_cases typed : datatype.spelling.val = xsdNonNegativeInteger
      · simp only [xsdNonNegativeInteger] at typed
        simp only [typed, decide_true, ↓reduceIte] at ran
        have finish : ∀ value : Usize, Rowl.Decimal.Bounded lexical.val 0 lexical.val.length 10000 value.val →
            (1 < lexical.val.length → lexical.val[0]? ≠ some 48#u8) →
            rdf_mapping.natural_up value .Zero = .ok n → NaturalNode n (objectView (.Literal ⟨lexical, .Datatype datatype⟩)) := by
          intro value bounded leading up
          have count := natural_up_spec value .Zero n up
          refine ⟨lexical.val, ?_, ?_⟩
          · rw [count]
            simpa [Rowl.Probes.naturalValue] using canonical_of_bounded lexical value.val bounded leading
          · simp [objectView, literalView, xsdNonNegativeInteger, typed]
        by_cases long : 1 < lexical.val.length
        · have longU : alloc.vec.Vec.len lexical > 1#usize := by scalar_tac
          have lookup : lexical.index_usize 0#usize = .ok lexical.val[0] := by
            simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem (show 0 < lexical.val.length by omega)]
          simp only [longU, ↓reduceIte, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
          by_cases zero : lexical.val[0] = 48#u8
          · simp [zero] at ran
          · simp only [zero, ↓reduceIte] at ran
            obtain ⟨o, readRun, ran⟩ := bind_eq_ok ran
            cases o with
            | none => simp at ran
            | some value =>
              simp only at ran
              obtain ⟨m, upRun, ran⟩ := bind_eq_ok ran
              simp only [Result.ok.injEq, Option.some.injEq] at ran
              subst ran
              have bounded := (Rowl.Decimal.read_bounded_some_iff lexical 0#usize _ _ value).mp readRun
              simp only [alloc.vec.Vec.len_val, rdf_mapping.CARDINALITY_LIMIT] at bounded
              have leading : 1 < lexical.val.length → lexical.val[0]? ≠ some 48#u8 := by
                intro _ head
                rw [List.getElem?_eq_getElem (show 0 < lexical.val.length by omega)] at head
                exact zero (Option.some.inj head)
              exact finish value (by simpa using bounded) leading upRun
        · have shortU : ¬ alloc.vec.Vec.len lexical > 1#usize := by scalar_tac
          simp only [shortU, ↓reduceIte] at ran
          obtain ⟨o, readRun, ran⟩ := bind_eq_ok ran
          cases o with
          | none => simp at ran
          | some value =>
            simp only at ran
            obtain ⟨m, upRun, ran⟩ := bind_eq_ok ran
            simp only [Result.ok.injEq, Option.some.injEq] at ran
            subst ran
            have bounded := (Rowl.Decimal.read_bounded_some_iff lexical 0#usize _ _ value).mp readRun
            simp only [alloc.vec.Vec.len_val, rdf_mapping.CARDINALITY_LIMIT] at bounded
            exact finish value (by simpa using bounded) (fun h => absurd h long) upRun
      · simp only [xsdNonNegativeInteger] at typed
        simp [typed] at ran

theorem node_true_spec (node : rdf.Object) (ran : rdf_mapping.node_true node = .ok true) :
    objectView node = trueNode := by
  rw [rdf_mapping.node_true.eq_def] at ran
  cases node with
  | Iri _ => simp at ran
  | Blank _ => simp at ran
  | Literal literal =>
    obtain ⟨lexical, kind⟩ := literal
    cases kind with
    | Language _ => simp at ran
    | Datatype datatype =>
      simp only [lift, bind_ok, same_correct, slice_val] at ran
      by_cases typed : datatype.spelling.val = xsdBoolean
      · simp only [xsdBoolean] at typed
        simp only [typed, decide_true, ↓reduceIte, Result.ok.injEq, decide_eq_true_eq] at ran
        simp [objectView, literalView, trueNode, ran, xsdBoolean, typed]
      · simp only [xsdBoolean] at typed
        simp [typed] at ran

theorem node_individual_spec (node : rdf.Object) (individual : model.Individual)
    (ran : rdf_mapping.node_individual node = .ok (some individual)) :
    objectView node = individualNode individual := by
  rw [rdf_mapping.node_individual.eq_def] at ran
  cases node with
  | Iri iri =>
    simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq] at ran
    subst ran
    simp [objectView, individualNode, iriNode]
  | Blank b =>
    simp only [Rowl.Nnf.copy_bytes_identity, bind_ok, Result.ok.injEq, Option.some.injEq] at ran
    subst ran
    simp [objectView, individualNode, anonymousNode]
  | Literal _ => simp at ran

theorem node_iri_spec (node : rdf.Object) (iri : model.Iri) (ran : rdf_mapping.node_iri node = .ok (some iri)) :
    objectView node = iriNode iri := by
  rw [rdf_mapping.node_iri.eq_def] at ran
  cases node with
  | Iri i =>
    simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq] at ran
    subst ran
    simp [objectView, iriNode]
  | Blank _ => simp at ran
  | Literal _ => simp at ran

theorem property_expression_spec (triples : alloc.vec.Vec rdf.Triple) (node : rdf.Object) (s s' : rdf_mapping.State)
    (role : model.ObjectPropertyExpression)
    (ran : rdf_mapping.property_expression triples node s = .ok (some (role, s'))) :
    ∃ patterns fresh, Grows triples.val s s' patterns fresh ∧
      ∀ rest, TOPE role (fresh ++ rest) (objectView node) patterns rest := by
  rw [rdf_mapping.property_expression.eq_def] at ran
  cases node with
  | Iri iri =>
    simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], grows_refl _ _, fun rest => by simpa [objectView, iriNode] using TOPE.named ⟨⟨iri.spelling⟩⟩ rest⟩
  | Literal _ => simp at ran
  | Blank b =>
    simp only [lift, bind_ok] at ran
    obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some index =>
      obtain ⟨t, unused, subject, predicate⟩ := find_spec _ _ _ _ _ _ findRun
      have lookup : triples.index_usize index = .ok t := by simp [alloc.vec.Vec.index_usize, unused.1]
      simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      cases object : t.object with
      | Blank _ => simp [object] at ran
      | Literal _ => simp [object] at ran
      | Iri iri =>
        simp only [object, take_correct, bind_ok] at ran
        obtain ⟨s1, recordRun, ran⟩ := bind_eq_ok ran
        simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        have g1 := grows_take triples.val s index t ⟨.blank b, owlInverseOf, .iri iri.spelling.val⟩ unused
          ⟨subject, by simpa [slice_val, owlInverseOf] using predicate, by simp [object, objectView]⟩
        have g2 := grows_record triples.val _ s1 b recordRun
        refine ⟨_, _, by simpa using grows_trans g1 g2, fun rest => ?_⟩
        simpa [objectView, iriNode] using TOPE.inverse ⟨⟨iri.spelling⟩⟩ b rest

/-! ### Data ranges -/

/-- Index lookup in a vector of indices. -/
private theorem index_at (firsts : alloc.vec.Vec Usize) (k : Usize) (inside : k.val < firsts.val.length) :
    firsts.index_usize k = .ok firsts.val[k.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]

/-- The element nodes of the cells `firsts[index..]`. -/
def elementsFrom (triples : List rdf.Triple) (firsts : List Usize) (index : Nat) : List Node :=
  (firsts.drop index).map (elementNode triples)

theorem elements_cons (triples : List rdf.Triple) (firsts : List Usize) (index : Nat) (inside : index < firsts.length) :
    elementsFrom triples firsts index = elementNode triples firsts[index] :: elementsFrom triples firsts (index + 1) := by
  rw [elementsFrom, elementsFrom, List.drop_eq_getElem_cons inside, List.map_cons]

theorem elements_end (triples : List rdf.Triple) (firsts : List Usize) (index : Nat) (beyond : firsts.length ≤ index) :
    elementsFrom triples firsts index = [] := by
  simp [elementsFrom, List.drop_eq_nil_iff.mpr beyond]

/-- The element of the cell `firsts[k]`, read. -/
private theorem element_at (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) (k : Usize)
    (node : rdf.Object) (inside : k.val < firsts.val.length)
    (ran : rdf_mapping.element triples firsts.val[k.val] = .ok (some node)) :
    objectView node = elementNode triples.val firsts.val[k.val] := element_spec triples _ node ran

theorem literal_members_spec (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (out values : alloc.vec.Vec model.Literal),
      rdf_mapping.literal_members triples firsts index out = .ok (some values) →
      ∃ news, values.val = out.val ++ news ∧
        List.Forall₂ LiteralNode news (elementsFrom triples.val firsts.val index.val) := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro out values ran
    rw [rdf_mapping.literal_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    exact ⟨[], by simp, by rw [elements_end _ _ _ (by omega)]; exact .nil⟩
  | succ n ih =>
    intro out values ran
    rw [rdf_mapping.literal_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts index more, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      simp only at ran
      obtain ⟨o1, literalRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some member =>
        simp only at ran
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out member room)
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, ↓reduceIte, push, advance,
            bind_ok] at ran
          obtain ⟨news, split, all⟩ := ih next (by omega) pushed values ran
          have view := element_at triples firsts index node more elementRun
          refine ⟨member :: news, by rw [split, contents]; simp, ?_⟩
          rw [elements_cons _ _ _ more, ← view]
          rw [nextIndex] at all
          exact .cons (node_literal_spec node member literalRun) all
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

theorem literal_list1_spec (triples : alloc.vec.Vec rdf.Triple) (node : rdf.Object) (s s' : rdf_mapping.State)
    (fuel : Usize) (values : model.NonEmpty model.Literal)
    (ran : rdf_mapping.literal_list1 triples node s fuel = .ok (some (values, s'))) :
    ∃ cells nodes, cells.length = (members1 values).length ∧ List.Forall₂ LiteralNode (members1 values) nodes ∧
      Grows triples.val s s' (listOf cells nodes).2 cells ∧ (listOf cells nodes).1 = objectView node := by
  rw [rdf_mapping.literal_list1] at ran
  obtain ⟨o, cellsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨firsts, s1⟩ := p
    obtain ⟨news, cells, split, lengths, grows, head⟩ := cells_spec triples fuel.val fuel node s s1 _ firsts rfl cellsRun
    simp at split
    by_cases nonempty : 1 ≤ firsts.val.length
    · have nonemptyU : alloc.vec.Vec.len firsts ≥ 1#usize := by scalar_tac
      have lookup0 := index_at firsts 0#usize (by simp; omega)
      simp [nonemptyU, nonempty, lookup0] at ran
      obtain ⟨o1, elementRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some one =>
        simp only at ran
        obtain ⟨o2, literalRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran
        | some first =>
          simp only at ran
          obtain ⟨o3, membersRun, ran⟩ := bind_eq_ok ran
          cases o3 with
          | none => simp at ran
          | some rest =>
            simp only [Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            obtain ⟨others, restIs, all⟩ := literal_members_spec triples firsts 1#usize _ rest membersRun
            have view := element_at triples firsts 0#usize one (by simp; omega) elementRun
            have restOthers : rest.val = others := by simpa using restIs
            have count := List.Forall₂.length_eq all
            simp only [elementsFrom, List.length_map, List.length_drop, show (1#usize).val = 1 from rfl] at count
            have cons0 := elements_cons triples.val firsts.val 0 (by omega)
            simp only [Nat.zero_add] at cons0
            have whole : news.map (elementNode triples.val) =
                elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 := by
              rw [← split]
              simp only [elementsFrom, List.drop_zero] at cons0 ⊢
              exact cons0
            refine ⟨cells, news.map (elementNode triples.val), ?_, ?_, grows, head⟩
            · simp only [members1, List.length_cons, restOthers]
              rw [lengths, ← split]
              omega
            · simp only [members1, restOthers]
              rw [whole]
              simp only [show (0#usize).val = 0 from rfl] at view
              have literal := node_literal_spec one first literalRun
              rw [view] at literal
              exact .cons literal (by simpa using all)
    · have noneU : ¬ alloc.vec.Vec.len firsts ≥ 1#usize := by scalar_tac
      simp [noneU, nonempty] at ran

/-- A triple about `b` with the predicate `word` that `find` returned, used. -/
theorem found_take (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (b : rdf.BlankNode) (key : Slice U8)
    (word : List U8) (named : key.val = word) (index : Usize)
    (findRun : rdf_mapping.find triples s.used b key 0#usize = .ok (some index)) :
    ∃ t, triples.index_usize index = .ok t ∧
      Grows triples.val s { s with used := s.used.set index true } [⟨.blank b, word, objectView t.object⟩] [] := by
  obtain ⟨t, unused, subject, predicate⟩ := find_spec _ _ _ _ _ _ findRun
  exact ⟨t, by simp [alloc.vec.Vec.index_usize, unused.1],
    grows_take triples.val s index t _ unused ⟨subject, by rw [predicate, named], rfl⟩⟩

theorem tfacets_length {fs : List model.FacetRestriction} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TFacets fs s ns ps s') : fs.length = ns.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simp [ih]

theorem facet_element_spec (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) (k : Usize)
    (s s' : rdf_mapping.State) (facet : model.FacetRestriction)
    (ran : rdf_mapping.facet_element triples firsts k s = .ok (some (facet, s'))) :
    ∃ (inside : k.val < firsts.val.length) (y : rdf.BlankNode) (v : Node),
      elementNode triples.val firsts.val[k.val] = .blank y ∧ LiteralNode facet.value v ∧
      Grows triples.val s s' [⟨.blank y, facet.facet.spelling.val, v⟩] [y] := by
  rw [rdf_mapping.facet_element] at ran
  by_cases inside : k.val < firsts.val.length
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts k inside, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts k node inside elementRun
      cases node with
      | Iri _ => simp at ran
      | Literal _ => simp at ran
      | Blank y =>
        simp only at ran
        obtain ⟨o1, anyRun, ran⟩ := bind_eq_ok ran
        cases o1 with
        | none => simp at ran
        | some found =>
          obtain ⟨t, unused, subject⟩ := find_any_spec _ _ _ _ _ anyRun
          have lookup : triples.index_usize found = .ok t := by simp [alloc.vec.Vec.index_usize, unused.1]
          simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
          obtain ⟨o2, literalRun, ran⟩ := bind_eq_ok ran
          cases o2 with
          | none => simp at ran
          | some value =>
            simp only [take_correct, bind_ok] at ran
            obtain ⟨s2, recordRun, ran⟩ := bind_eq_ok ran
            simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            have g1 := grows_take triples.val s found t ⟨.blank y, t.predicate.spelling.val, objectView t.object⟩
              unused ⟨subject, rfl, rfl⟩
            have g2 := grows_record triples.val _ s2 y recordRun
            refine ⟨inside, y, objectView t.object, by simpa [objectView] using view.symm,
              node_literal_spec _ _ literalRun, ?_⟩
            simpa using grows_trans g1 g2
  · simp [UScalar.lt_equiv, inside] at ran

theorem facet_members_spec (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (out values : alloc.vec.Vec model.FacetRestriction),
      rdf_mapping.facet_members triples firsts index s out = .ok (some (values, s')) →
      ∃ news patterns fresh, values.val = out.val ++ news ∧ Grows triples.val s s' patterns fresh ∧
        ∀ rest, TFacets news (fresh ++ rest) (elementsFrom triples.val firsts.val index.val) patterns rest := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro s s' out values ran
    rw [rdf_mapping.facet_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], [], by simp, grows_refl _ _, fun rest => by
      rw [elements_end _ _ _ (by omega)]; exact .nil rest⟩
  | succ n ih =>
    intro s s' out values ran
    rw [rdf_mapping.facet_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some p =>
      obtain ⟨member, s1⟩ := p
      obtain ⟨_, y, v, view, literal, grows⟩ := facet_element_spec triples firsts index s s1 member elementRun
      by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out member room)
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = index.val + 1 := by simpa using nextValue
        simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance] at ran
        obtain ⟨news, patterns, fresh, split, grows', facets⟩ := ih next (by omega) s1 s' pushed values ran
        refine ⟨member :: news, _ :: patterns, y :: fresh, by rw [split, contents]; simp,
          by simpa using grows_trans grows grows', fun rest => ?_⟩
        rw [elements_cons _ _ _ more, view]
        rw [nextIndex] at facets
        exact .cons member news y (fresh ++ rest) rest v _ patterns literal (facets rest)
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

/-- The data range reader is right at a fuel. -/
def RangeRight (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared) (fuel : Usize) :
    Prop :=
  ∀ (node : rdf.Object) (s s' : rdf_mapping.State) (r : model.DataRange),
    rdf_mapping.data_range triples kinds node s fuel = .ok (some (r, s')) →
    ∃ patterns fresh, Grows triples.val s s' patterns fresh ∧
      ∀ rest, TDR r (fresh ++ rest) (objectView node) patterns rest

theorem range_element_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : RangeRight triples kinds fuel) (firsts : alloc.vec.Vec Usize) (k : Usize)
    (s s' : rdf_mapping.State) (r : model.DataRange)
    (ran : rdf_mapping.range_element triples kinds firsts k s fuel = .ok (some (r, s'))) :
    ∃ (inside : k.val < firsts.val.length) (patterns : List Pattern) (fresh : List rdf.BlankNode),
      Grows triples.val s s' patterns fresh ∧
      ∀ rest, TDR r (fresh ++ rest) (elementNode triples.val firsts.val[k.val]) patterns rest := by
  rw [rdf_mapping.range_element] at ran
  by_cases inside : k.val < firsts.val.length
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts k inside, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts k node inside elementRun
      obtain ⟨patterns, fresh, grows, tdr⟩ := right node s s' r ran
      exact ⟨inside, patterns, fresh, grows, fun rest => by rw [← view]; exact tdr rest⟩
  · simp [UScalar.lt_equiv, inside] at ran

theorem range_members_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : RangeRight triples kinds fuel) (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (out values : alloc.vec.Vec model.DataRange),
      rdf_mapping.range_members triples kinds firsts index s out fuel = .ok (some (values, s')) →
      ∃ news patterns fresh, values.val = out.val ++ news ∧ news.length = firsts.val.length - index.val ∧
        Grows triples.val s s' patterns fresh ∧
        ∀ rest, ∃ nodes, nodes = elementsFrom triples.val firsts.val index.val ∧
          TDRs news (fresh ++ rest) nodes patterns rest := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro s s' out values ran
    rw [rdf_mapping.range_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], [], by simp, by simp, grows_refl _ _,
      fun rest => ⟨[], by rw [elements_end _ _ _ (by omega)], .nil rest⟩⟩
  | succ n ih =>
    intro s s' out values ran
    rw [rdf_mapping.range_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts index more, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts index node more elementRun
      simp only at ran
      obtain ⟨o1, rangeRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some p =>
        obtain ⟨member, s1⟩ := p
        obtain ⟨p1, f1, grows, tdr⟩ := right node s s1 member rangeRun
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out member room)
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance] at ran
          obtain ⟨news, patterns, fresh, split, count, grows', tdrs⟩ := ih next (by omega) s1 s' pushed values ran
          refine ⟨member :: news, p1 ++ patterns, f1 ++ fresh, by rw [split, contents]; simp,
            by simp only [List.length_cons]; omega, grows_trans grows grows', fun rest => ?_⟩
          obtain ⟨nodes, nodesIs, tail⟩ := tdrs rest
          refine ⟨elementNode triples.val firsts.val[index.val] :: nodes, by rw [elements_cons _ _ _ more, nodesIs,
            nextIndex], ?_⟩
          rw [List.append_assoc]
          have head := tdr (fresh ++ rest)
          rw [view] at head
          exact .cons member news _ _ _ _ nodes p1 patterns head tail
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

theorem range_list2_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : RangeRight triples kinds fuel) (node : rdf.Object) (s s' : rdf_mapping.State)
    (xs : model.AtLeastTwo model.DataRange)
    (ran : rdf_mapping.range_list2 triples kinds node s fuel = .ok (some (xs, s'))) :
    ∃ cells nodes patterns fresh, cells.length = (members2 xs).length ∧
      Grows triples.val s s' ((listOf cells nodes).2 ++ patterns) (cells ++ fresh) ∧
      (listOf cells nodes).1 = objectView node ∧ ∀ rest, TDRs (members2 xs) (fresh ++ rest) nodes patterns rest := by
  rw [rdf_mapping.range_list2] at ran
  obtain ⟨o, cellsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨firsts, s1⟩ := p
    obtain ⟨news, cells, split, lengths, grows, head⟩ := cells_spec triples fuel.val fuel node s s1 _ firsts rfl cellsRun
    simp at split
    simp only at ran
    obtain ⟨o1, firstRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p1 =>
      obtain ⟨first, s2⟩ := p1
      obtain ⟨inside0, ps1, f1, grows1, tdr1⟩ := range_element_spec triples kinds fuel right firsts 0#usize s1 s2 first
        firstRun
      simp only at ran
      obtain ⟨o2, secondRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p2 =>
        obtain ⟨second, s3⟩ := p2
        obtain ⟨inside1, ps2, f2, grows2, tdr2⟩ := range_element_spec triples kinds fuel right firsts 1#usize s2 s3
          second secondRun
        simp only at ran
        obtain ⟨o3, membersRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some p3 =>
          obtain ⟨others, s4⟩ := p3
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          obtain ⟨news3, ps3, f3, restIs, count3, grows3, tdrs3⟩ := range_members_spec triples kinds fuel right firsts
            2#usize s3 s4 _ others membersRun
          simp at restIs
          simp only [show (0#usize).val = 0 from rfl] at inside0 tdr1
          simp only [show (1#usize).val = 1 from rfl] at inside1 tdr2
          simp only [show (2#usize).val = 2 from rfl] at count3 tdrs3
          have c0 : elementsFrom triples.val firsts.val 0 =
              elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 :=
            elements_cons triples.val firsts.val 0 (by omega)
          have c1 : elementsFrom triples.val firsts.val 1 =
              elementNode triples.val firsts.val[1] :: elementsFrom triples.val firsts.val 2 :=
            elements_cons triples.val firsts.val 1 (by omega)
          have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
            simp [elementsFrom, split]
          refine ⟨cells, news.map (elementNode triples.val), ps1 ++ (ps2 ++ ps3), f1 ++ (f2 ++ f3), ?_, ?_, head,
            fun rest => ?_⟩
          · simp only [members2, List.length_cons, restIs]
            rw [lengths, ← split]
            omega
          · simpa [List.append_assoc] using grows_trans (grows_trans (grows_trans grows grows1) grows2) grows3
          · obtain ⟨nodes, nodesIs, tail⟩ := tdrs3 rest
            rw [nodesIs] at tail
            rw [start, c0, c1]
            simp only [members2, restIs, List.append_assoc]
            exact .cons first (second :: news3) _ _ _ _ _ ps1 (ps2 ++ ps3) (tdr1 _)
              (.cons second news3 _ _ _ _ _ ps2 ps3 (tdr2 _) tail)

theorem range_construct_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : RangeRight triples kinds fuel) (blank : rdf.BlankNode) (s s' : rdf_mapping.State)
    (r : model.DataRange) (ran : rdf_mapping.range_construct triples kinds blank s fuel = .ok (some (r, s'))) :
    ∃ patterns fresh, Grows triples.val s s' patterns fresh ∧
      ∀ rest, TDR r (blank :: (fresh ++ rest)) (.blank blank)
        (⟨.blank blank, rdfType, .iri rdfsDatatype⟩ :: patterns) rest := by
  rw [rdf_mapping.range_construct] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlIntersectionOf
      (by simp [slice_val, owlIntersectionOf]) index findRun
    simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, listRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p =>
      obtain ⟨members, s2⟩ := p
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨cells, nodes, patterns, fresh, lengths, grows2, head, tdrs⟩ := range_list2_spec triples kinds fuel right
        t.object _ s2 members listRun
      refine ⟨_ :: ((listOf cells nodes).2 ++ patterns), cells ++ fresh, by simpa using grows_trans grows1 grows2,
        fun rest => ?_⟩
      have tdr := TDR.intersection members blank cells (fresh ++ rest) rest nodes patterns lengths (tdrs rest)
      rw [head] at tdr
      simpa only [List.append_assoc] using tdr
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlUnionOf
        (by simp [slice_val, owlUnionOf]) index findRun1
      simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, listRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p =>
        obtain ⟨members, s2⟩ := p
        simp [Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        obtain ⟨cells, nodes, patterns, fresh, lengths, grows2, head, tdrs⟩ := range_list2_spec triples kinds fuel
          right t.object _ s2 members listRun
        refine ⟨_ :: ((listOf cells nodes).2 ++ patterns), cells ++ fresh, by simpa using grows_trans grows1 grows2,
          fun rest => ?_⟩
        have tdr := TDR.union members blank cells (fresh ++ rest) rest nodes patterns lengths (tdrs rest)
        rw [head] at tdr
        simpa only [List.append_assoc] using tdr
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlDatatypeComplementOf
          (by simp [slice_val, owlDatatypeComplementOf]) index findRun2
        simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, innerRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some p =>
          obtain ⟨inner, s2⟩ := p
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          obtain ⟨patterns, fresh, grows2, tdr⟩ := right t.object _ s2 inner innerRun
          exact ⟨_ :: patterns, fresh, by simpa using grows_trans grows1 grows2,
            fun rest => TDR.complement inner blank (fresh ++ rest) rest _ patterns (tdr rest)⟩
      | none =>
        simp only at ran
        obtain ⟨o3, findRun3, ran⟩ := bind_eq_ok ran
        cases o3 with
        | some index =>
          obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlOneOf
            (by simp [slice_val, owlOneOf]) index findRun3
          simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
          obtain ⟨o4, listRun, ran⟩ := bind_eq_ok ran
          cases o4 with
          | none => simp at ran
          | some p =>
            obtain ⟨members, s2⟩ := p
            simp [Result.ok.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            obtain ⟨cells, nodes, lengths, literals, grows2, head⟩ := literal_list1_spec triples t.object _ s2 fuel
              members listRun
            refine ⟨_ :: (listOf cells nodes).2, cells, by simpa using grows_trans grows1 grows2, fun rest => ?_⟩
            have tdr := TDR.oneOf members blank cells rest nodes lengths literals
            rw [head] at tdr
            exact tdr
        | none =>
          simp only at ran
          obtain ⟨o4, findRun4, ran⟩ := bind_eq_ok ran
          cases o4 with
          | none => simp at ran
          | some index =>
            obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlOnDatatype
              (by simp [slice_val, owlOnDatatype]) index findRun4
            simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
            obtain ⟨o5, iriRun, ran⟩ := bind_eq_ok ran
            cases o5 with
            | none => simp at ran
            | some base =>
              have baseView := node_iri_spec t.object base iriRun
              simp only [take_correct, bind_ok] at ran
              obtain ⟨o6, findRun6, ran⟩ := bind_eq_ok ran
              cases o6 with
              | none => simp at ran
              | some list =>
                obtain ⟨t1, lookup1, grows2⟩ := found_take triples { s with used := s.used.set index true } blank _
                  owlWithRestrictions (by simp [slice_val, owlWithRestrictions]) list findRun6
                simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup1, bind_ok] at ran
                obtain ⟨o7, cellsRun, ran⟩ := bind_eq_ok ran
                cases o7 with
                | none => simp at ran
                | some p =>
                  obtain ⟨firsts, s3⟩ := p
                  obtain ⟨news, cells, split, lengths, grows3, head⟩ := cells_spec triples fuel.val fuel t1.object _ s3
                    _ firsts rfl cellsRun
                  simp at split
                  simp only at ran
                  obtain ⟨o8, elementRun, ran⟩ := bind_eq_ok ran
                  cases o8 with
                  | none => simp at ran
                  | some p1 =>
                    obtain ⟨first, s4⟩ := p1
                    obtain ⟨inside0, y, v, view, literal, grows4⟩ := facet_element_spec triples firsts 0#usize s3 s4
                      first elementRun
                    simp only at ran
                    obtain ⟨o9, membersRun, ran⟩ := bind_eq_ok ran
                    cases o9 with
                    | none => simp at ran
                    | some p2 =>
                      obtain ⟨others, s5⟩ := p2
                      simp [Result.ok.injEq] at ran
                      obtain ⟨rfl, rfl⟩ := ran
                      obtain ⟨news2, ps2, f2, restIs, grows5, facets⟩ := facet_members_spec triples firsts 1#usize s4 s5
                        _ others membersRun
                      simp at restIs
                      simp only [show (0#usize).val = 0 from rfl] at inside0 view
                      simp only [show (1#usize).val = 1 from rfl] at facets
                      have c0 : elementsFrom triples.val firsts.val 0 =
                          elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 :=
                        elements_cons triples.val firsts.val 0 (by omega)
                      have whole : news.map (elementNode triples.val) = .blank y :: elementsFrom triples.val firsts.val 1 := by
                        have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
                          simp [elementsFrom, split]
                        rw [start, c0, view]
                      have n2 := tfacets_length (facets [])
                      simp only [elementsFrom, List.length_map, List.length_drop] at n2
                      have count : cells.length =
                          (members1 (⟨first, others⟩ : model.NonEmpty model.FacetRestriction)).length := by
                        simp only [members1, List.length_cons, restIs]
                        rw [lengths, ← split]
                        omega
                      refine ⟨⟨.blank blank, owlOnDatatype, objectView t.object⟩ ::
                          ⟨.blank blank, owlWithRestrictions, objectView t1.object⟩ ::
                          ((listOf cells (news.map (elementNode triples.val))).2 ++
                            (⟨.blank y, first.facet.spelling.val, v⟩ :: ps2)),
                        cells ++ (y :: f2), ?_, fun rest => ?_⟩
                      · simpa using grows_trans (grows_trans (grows_trans (grows_trans grows1 grows2) grows3) grows4)
                          grows5
                      · have tfs : TFacets (members1 (⟨first, others⟩ : model.NonEmpty model.FacetRestriction))
                            (y :: (f2 ++ rest)) (news.map (elementNode triples.val))
                            (⟨.blank y, first.facet.spelling.val, v⟩ :: ps2) rest := by
                          rw [whole]
                          simp only [members1, restIs]
                          exact .cons first news2 y (f2 ++ rest) rest v _ ps2 literal (facets rest)
                        have tdr := TDR.restriction ⟨base⟩ ⟨first, others⟩ blank cells (y :: (f2 ++ rest)) rest _ _
                          count tfs
                        rw [head, ← baseView] at tdr
                        simpa only [List.append_assoc, List.cons_append] using tdr

theorem data_range_step (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (below : ∀ (i : Usize), i.val + 1 = fuel.val → RangeRight triples kinds i) :
    RangeRight triples kinds fuel := by
  intro node s s' r ran
  rw [rdf_mapping.data_range.eq_def] at ran
  cases node with
  | Iri iri =>
    simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], grows_refl _ _, fun rest => by simpa [objectView, iriNode] using TDR.datatype ⟨⟨iri.spelling⟩⟩ rest⟩
  | Literal _ => simp at ran
  | Blank b =>
    by_cases positive : fuel > 0#usize
    · simp only [positive, ↓reduceIte, lift, bind_ok] at ran
      obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
      cases o with
      | none => simp at ran
      | some index =>
        obtain ⟨t, unused, subject, predicate, object⟩ := find_type_spec _ _ _ _ _ _ findRun
        simp only [take_correct, bind_ok] at ran
        obtain ⟨s2, recordRun, ran⟩ := bind_eq_ok ran
        obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
        have fewerIs : fewer.val + 1 = fuel.val := by
          have : fuel.val > 0 := by scalar_tac
          simp at fewerValue
          omega
        simp only [back, bind_ok] at ran
        obtain ⟨patterns, fresh, grows, tdr⟩ := range_construct_spec triples kinds fewer (below fewer fewerIs) b s2 s' r
          ran
        have g1 := grows_take triples.val s index t ⟨.blank b, rdfType, .iri rdfsDatatype⟩ unused
          ⟨subject, predicate, by simpa [slice_val, rdfsDatatype] using object⟩
        have g2 := grows_record triples.val _ s2 b recordRun
        exact ⟨_ :: patterns, b :: fresh, by simpa using grows_trans (grows_trans g1 g2) grows,
          fun rest => by simpa [objectView] using tdr rest⟩
    · simp [positive] at ran

theorem data_range_right (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared) :
    ∀ (fuel : Usize), RangeRight triples kinds fuel := by
  have every : ∀ (n : Nat) (fuel : Usize), fuel.val = n → RangeRight triples kinds fuel := by
    intro n
    induction n with
    | zero => intro fuel same; exact data_range_step triples kinds fuel (fun i h => by omega)
    | succ n ih => intro fuel same; exact data_range_step triples kinds fuel (fun i h => ih i (by omega))
  exact fun fuel => every fuel.val fuel rfl

/-! ### Restrictions on data properties and lists of individuals -/

/-- A data property restriction read after its `rdf:type` and `owl:onProperty`
    triples: its own triples `head`, then those of its data range `tail`. -/
def DataRestrictionOk (triples : alloc.vec.Vec rdf.Triple) (blank : rdf.BlankNode) (property : model.DataProperty)
    (s s' : rdf_mapping.State) (c : model.ClassExpression) : Prop :=
  ∃ head tail fresh, Grows triples.val s s' (head ++ tail) fresh ∧
    ∀ rest, TCE c (blank :: (fresh ++ rest)) (.blank blank)
      (restrictionHead blank (iriNode property.iri) ++ (head ++ tail)) rest

theorem on_data_range_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (blank : rdf.BlankNode) (s s' : rdf_mapping.State) (fuel : Usize) (range : model.DataRange)
    (ran : rdf_mapping.on_data_range triples kinds blank s fuel = .ok (some (range, s'))) :
    ∃ r patterns fresh, Grows triples.val s s' (⟨.blank blank, owlOnDataRange, r⟩ :: patterns) fresh ∧
      ∀ rest, TDR range (fresh ++ rest) r patterns rest := by
  rw [rdf_mapping.on_data_range] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlOnDataRange
      (by simp [slice_val, owlOnDataRange]) index findRun
    simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨patterns, fresh, grows2, tdr⟩ := data_range_right triples kinds fuel t.object _ s' range ran
    exact ⟨objectView t.object, patterns, fresh, by simpa using grows_trans grows1 grows2, tdr⟩

theorem data_qualified_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (blank : rdf.BlankNode) (property : model.DataProperty) (s s' : rdf_mapping.State) (fuel : Usize)
    (c : model.ClassExpression)
    (ran : rdf_mapping.data_qualified triples kinds blank property s fuel = .ok (some (c, s'))) :
    DataRestrictionOk triples blank property s s' c := by
  rw [rdf_mapping.data_qualified] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMinQualifiedCardinality
      (by simp [slice_val, owlMinQualifiedCardinality]) index findRun
    simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, naturalRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some n =>
      simp only [take_correct, bind_ok] at ran
      obtain ⟨o2, rangeRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p =>
        obtain ⟨range, s2⟩ := p
        simp [Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        obtain ⟨r, patterns, fresh, grows2, tdr⟩ := on_data_range_spec triples kinds blank _ s2 fuel range rangeRun
        exact ⟨[⟨.blank blank, owlMinQualifiedCardinality, objectView t.object⟩, ⟨.blank blank, owlOnDataRange, r⟩],
          patterns, fresh, by simpa using grows_trans grows1 grows2, fun rest => by
            simpa using TCE.dataMinQualified n property range blank (fresh ++ rest) rest _ r patterns
              (node_natural_spec _ n naturalRun) (tdr rest)⟩
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMaxQualifiedCardinality
        (by simp [slice_val, owlMaxQualifiedCardinality]) index findRun1
      simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, naturalRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some n =>
        simp only [take_correct, bind_ok] at ran
        obtain ⟨o3, rangeRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some p =>
          obtain ⟨range, s2⟩ := p
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          obtain ⟨r, patterns, fresh, grows2, tdr⟩ := on_data_range_spec triples kinds blank _ s2 fuel range rangeRun
          exact ⟨[⟨.blank blank, owlMaxQualifiedCardinality, objectView t.object⟩, ⟨.blank blank, owlOnDataRange, r⟩],
            patterns, fresh, by simpa using grows_trans grows1 grows2, fun rest => by
              simpa using TCE.dataMaxQualified n property range blank (fresh ++ rest) rest _ r patterns
                (node_natural_spec _ n naturalRun) (tdr rest)⟩
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlQualifiedCardinality
          (by simp [slice_val, owlQualifiedCardinality]) index findRun2
        simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, naturalRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some n =>
          simp only [take_correct, bind_ok] at ran
          obtain ⟨o4, rangeRun, ran⟩ := bind_eq_ok ran
          cases o4 with
          | none => simp at ran
          | some p =>
            obtain ⟨range, s2⟩ := p
            simp [Result.ok.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            obtain ⟨r, patterns, fresh, grows2, tdr⟩ := on_data_range_spec triples kinds blank _ s2 fuel range
              rangeRun
            exact ⟨[⟨.blank blank, owlQualifiedCardinality, objectView t.object⟩, ⟨.blank blank, owlOnDataRange, r⟩],
              patterns, fresh, by simpa using grows_trans grows1 grows2, fun rest => by
                simpa using TCE.dataExactQualified n property range blank (fresh ++ rest) rest _ r patterns
                  (node_natural_spec _ n naturalRun) (tdr rest)⟩

theorem data_cardinality_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (blank : rdf.BlankNode) (property : model.DataProperty) (s s' : rdf_mapping.State) (fuel : Usize)
    (c : model.ClassExpression)
    (ran : rdf_mapping.data_cardinality triples kinds blank property s fuel = .ok (some (c, s'))) :
    DataRestrictionOk triples blank property s s' c := by
  rw [rdf_mapping.data_cardinality] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMinCardinality
      (by simp [slice_val, owlMinCardinality]) index findRun
    simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, naturalRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some n =>
      simp [take_correct, Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨[⟨.blank blank, owlMinCardinality, objectView t.object⟩], [], [], by simpa using grows1, fun rest => by
        simpa using TCE.dataMin n property blank rest _ (node_natural_spec _ n naturalRun)⟩
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMaxCardinality
        (by simp [slice_val, owlMaxCardinality]) index findRun1
      simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, naturalRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some n =>
        simp [take_correct, Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        exact ⟨[⟨.blank blank, owlMaxCardinality, objectView t.object⟩], [], [], by simpa using grows1, fun rest => by
          simpa using TCE.dataMax n property blank rest _ (node_natural_spec _ n naturalRun)⟩
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => exact data_qualified_spec triples kinds blank property s s' fuel c ran
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlCardinality
          (by simp [slice_val, owlCardinality]) index findRun2
        simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, naturalRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some n =>
          simp [take_correct, Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          exact ⟨[⟨.blank blank, owlCardinality, objectView t.object⟩], [], [], by simpa using grows1, fun rest => by
            simpa using TCE.dataExact n property blank rest _ (node_natural_spec _ n naturalRun)⟩

theorem data_restriction_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (blank : rdf.BlankNode) (property : model.DataProperty) (s s' : rdf_mapping.State) (fuel : Usize)
    (c : model.ClassExpression)
    (ran : rdf_mapping.data_restriction triples kinds blank property s fuel = .ok (some (c, s'))) :
    DataRestrictionOk triples blank property s s' c := by
  rw [rdf_mapping.data_restriction] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlSomeValuesFrom
      (by simp [slice_val, owlSomeValuesFrom]) index findRun
    simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, rangeRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p =>
      obtain ⟨range, s2⟩ := p
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨patterns, fresh, grows2, tdr⟩ := data_range_right triples kinds fuel t.object _ s2 range rangeRun
      exact ⟨[⟨.blank blank, owlSomeValuesFrom, objectView t.object⟩], patterns, fresh,
        by simpa using grows_trans grows1 grows2,
        fun rest => by simpa using TCE.dataSome property range blank (fresh ++ rest) rest _ patterns (tdr rest)⟩
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlAllValuesFrom
        (by simp [slice_val, owlAllValuesFrom]) index findRun1
      simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, rangeRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p =>
        obtain ⟨range, s2⟩ := p
        simp [Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        obtain ⟨patterns, fresh, grows2, tdr⟩ := data_range_right triples kinds fuel t.object _ s2 range rangeRun
        exact ⟨[⟨.blank blank, owlAllValuesFrom, objectView t.object⟩], patterns, fresh,
          by simpa using grows_trans grows1 grows2,
          fun rest => by simpa using TCE.dataAll property range blank (fresh ++ rest) rest _ patterns (tdr rest)⟩
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => exact data_cardinality_spec triples kinds blank property s s' fuel c ran
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlHasValue
          (by simp [slice_val, owlHasValue]) index findRun2
        simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, literalRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some value =>
          simp [take_correct, Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          exact ⟨[⟨.blank blank, owlHasValue, objectView t.object⟩], [], [], by simpa using grows1, fun rest => by
            simpa using TCE.dataHasValue property value blank rest _ (node_literal_spec _ value literalRun)⟩

theorem individual_members_spec (triples : alloc.vec.Vec rdf.Triple) (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (out values : alloc.vec.Vec model.Individual),
      rdf_mapping.individual_members triples firsts index out = .ok (some values) →
      ∃ news, values.val = out.val ++ news ∧
        news.map individualNode = elementsFrom triples.val firsts.val index.val := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro out values ran
    rw [rdf_mapping.individual_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    exact ⟨[], by simp, by rw [elements_end _ _ _ (by omega)]; rfl⟩
  | succ n ih =>
    intro out values ran
    rw [rdf_mapping.individual_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts index more, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      simp only at ran
      obtain ⟨o1, individualRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some member =>
        simp only at ran
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out member room)
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, ↓reduceIte, push, advance,
            bind_ok] at ran
          obtain ⟨news, split, all⟩ := ih next (by omega) pushed values ran
          have view := element_at triples firsts index node more elementRun
          refine ⟨member :: news, by rw [split, contents]; simp, ?_⟩
          rw [elements_cons _ _ _ more, ← view, List.map_cons, all, nextIndex,
            node_individual_spec node member individualRun]
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

theorem individual_list1_spec (triples : alloc.vec.Vec rdf.Triple) (node : rdf.Object) (s s' : rdf_mapping.State)
    (fuel : Usize) (values : model.NonEmpty model.Individual)
    (ran : rdf_mapping.individual_list1 triples node s fuel = .ok (some (values, s'))) :
    ∃ cells, cells.length = (members1 values).length ∧
      Grows triples.val s s' (listOf cells ((members1 values).map individualNode)).2 cells ∧
      (listOf cells ((members1 values).map individualNode)).1 = objectView node := by
  rw [rdf_mapping.individual_list1] at ran
  obtain ⟨o, cellsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨firsts, s1⟩ := p
    obtain ⟨news, cells, split, lengths, grows, head⟩ := cells_spec triples fuel.val fuel node s s1 _ firsts rfl cellsRun
    simp at split
    by_cases nonempty : 1 ≤ firsts.val.length
    · have nonemptyU : alloc.vec.Vec.len firsts ≥ 1#usize := by scalar_tac
      have lookup0 := index_at firsts 0#usize (by simp; omega)
      simp [nonemptyU, nonempty, lookup0] at ran
      obtain ⟨o1, elementRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some one =>
        simp only at ran
        obtain ⟨o2, individualRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran
        | some first =>
          simp only at ran
          obtain ⟨o3, membersRun, ran⟩ := bind_eq_ok ran
          cases o3 with
          | none => simp at ran
          | some rest =>
            simp only [Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            obtain ⟨others, restIs, all⟩ := individual_members_spec triples firsts 1#usize _ rest membersRun
            have view := element_at triples firsts 0#usize one (by simp; omega) elementRun
            have restOthers : rest.val = others := by simpa using restIs
            simp only [show (0#usize).val = 0 from rfl] at view
            simp only [show (1#usize).val = 1 from rfl] at all
            have c0 : elementsFrom triples.val firsts.val 0 =
                elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 :=
              elements_cons triples.val firsts.val 0 (by omega)
            have e0 : elementNode triples.val firsts.val[0] = individualNode first := by
              rw [← node_individual_spec one first individualRun]
              exact view.symm
            have whole : (members1 (⟨first, rest⟩ : model.NonEmpty model.Individual)).map individualNode =
                news.map (elementNode triples.val) := by
              have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
                simp [elementsFrom, split]
              rw [start, c0, e0, ← all]
              simp [members1, restOthers]
            have count : others.length = firsts.val.length - 1 := by
              have := congrArg List.length all
              simpa [elementsFrom] using this
            refine ⟨cells, ?_, by rw [whole]; exact grows, by rw [whole]; exact head⟩
            simp only [members1, List.length_cons, restOthers]
            rw [lengths, ← split]
            omega
    · have noneU : ¬ alloc.vec.Vec.len firsts ≥ 1#usize := by scalar_tac
      simp [noneU, nonempty] at ran

/-! ### Class expressions -/

/-- The class expression reader is right at a fuel. -/
def ClassRight (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared) (fuel : Usize) :
    Prop :=
  ∀ (node : rdf.Object) (s s' : rdf_mapping.State) (c : model.ClassExpression),
    rdf_mapping.class_expression triples kinds node s fuel = .ok (some (c, s')) →
    ∃ patterns fresh, Grows triples.val s s' patterns fresh ∧
      ∀ rest, TCE c (fresh ++ rest) (objectView node) patterns rest

/-- An object property restriction read after its `rdf:type` and
    `owl:onProperty` triples, on a property expression with node `n1`, triples
    `p1` and blank nodes `f1`: its own triples `head`, then those of its filler
    `tail`. -/
def ObjectRestrictionOk (triples : alloc.vec.Vec rdf.Triple) (blank : rdf.BlankNode) (n1 : Node)
    (p1 : List Pattern) (f1 : Supply) (s s' : rdf_mapping.State) (c : model.ClassExpression) : Prop :=
  ∃ head tail fresh, Grows triples.val s s' (head ++ tail) fresh ∧
    ∀ rest, TCE c (blank :: (f1 ++ (fresh ++ rest))) (.blank blank)
      (restrictionHead blank n1 ++ (head ++ (p1 ++ tail))) rest

theorem on_class_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (blank : rdf.BlankNode) (s s' : rdf_mapping.State)
    (c : model.ClassExpression) (ran : rdf_mapping.on_class triples kinds blank s fuel = .ok (some (c, s'))) :
    ∃ n2 patterns fresh, Grows triples.val s s' (⟨.blank blank, owlOnClass, n2⟩ :: patterns) fresh ∧
      ∀ rest, TCE c (fresh ++ rest) n2 patterns rest := by
  rw [rdf_mapping.on_class] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlOnClass
      (by simp [slice_val, owlOnClass]) index findRun
    simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨patterns, fresh, grows2, tce⟩ := right t.object _ s' c ran
    exact ⟨objectView t.object, patterns, fresh, by simpa using grows_trans grows1 grows2, tce⟩

theorem object_qualified_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (blank : rdf.BlankNode)
    (role : model.ObjectPropertyExpression) (n1 : Node) (p1 : List Pattern) (f1 : Supply)
    (roleOk : ∀ rest, TOPE role (f1 ++ rest) n1 p1 rest) (s s' : rdf_mapping.State) (c : model.ClassExpression)
    (ran : rdf_mapping.object_qualified triples kinds blank role s fuel = .ok (some (c, s'))) :
    ObjectRestrictionOk triples blank n1 p1 f1 s s' c := by
  rw [rdf_mapping.object_qualified] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMinQualifiedCardinality
      (by simp [slice_val, owlMinQualifiedCardinality]) index findRun
    simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, naturalRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some n =>
      simp only [take_correct, bind_ok] at ran
      obtain ⟨o2, classRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p =>
        obtain ⟨filler, s2⟩ := p
        simp [Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        obtain ⟨n2, patterns, fresh, grows2, tce⟩ := on_class_spec triples kinds fuel right blank _ s2 filler classRun
        exact ⟨[⟨.blank blank, owlMinQualifiedCardinality, objectView t.object⟩, ⟨.blank blank, owlOnClass, n2⟩],
          patterns, fresh, by simpa using grows_trans grows1 grows2, fun rest => by
            simpa using TCE.minQualified n role filler blank (f1 ++ (fresh ++ rest)) (fresh ++ rest) rest n1 n2 _ p1
              patterns (roleOk _) (node_natural_spec _ n naturalRun) (tce rest)⟩
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMaxQualifiedCardinality
        (by simp [slice_val, owlMaxQualifiedCardinality]) index findRun1
      simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, naturalRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some n =>
        simp only [take_correct, bind_ok] at ran
        obtain ⟨o3, classRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some p =>
          obtain ⟨filler, s2⟩ := p
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          obtain ⟨n2, patterns, fresh, grows2, tce⟩ := on_class_spec triples kinds fuel right blank _ s2 filler
            classRun
          exact ⟨[⟨.blank blank, owlMaxQualifiedCardinality, objectView t.object⟩, ⟨.blank blank, owlOnClass, n2⟩],
            patterns, fresh, by simpa using grows_trans grows1 grows2, fun rest => by
              simpa using TCE.maxQualified n role filler blank (f1 ++ (fresh ++ rest)) (fresh ++ rest) rest n1 n2 _
                p1 patterns (roleOk _) (node_natural_spec _ n naturalRun) (tce rest)⟩
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlQualifiedCardinality
          (by simp [slice_val, owlQualifiedCardinality]) index findRun2
        simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, naturalRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some n =>
          simp only [take_correct, bind_ok] at ran
          obtain ⟨o4, classRun, ran⟩ := bind_eq_ok ran
          cases o4 with
          | none => simp at ran
          | some p =>
            obtain ⟨filler, s2⟩ := p
            simp [Result.ok.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            obtain ⟨n2, patterns, fresh, grows2, tce⟩ := on_class_spec triples kinds fuel right blank _ s2 filler
              classRun
            exact ⟨[⟨.blank blank, owlQualifiedCardinality, objectView t.object⟩, ⟨.blank blank, owlOnClass, n2⟩],
              patterns, fresh, by simpa using grows_trans grows1 grows2, fun rest => by
                simpa using TCE.exactQualified n role filler blank (f1 ++ (fresh ++ rest)) (fresh ++ rest) rest n1 n2
                  _ p1 patterns (roleOk _) (node_natural_spec _ n naturalRun) (tce rest)⟩

theorem object_cardinality_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (blank : rdf.BlankNode)
    (role : model.ObjectPropertyExpression) (n1 : Node) (p1 : List Pattern) (f1 : Supply)
    (roleOk : ∀ rest, TOPE role (f1 ++ rest) n1 p1 rest) (s s' : rdf_mapping.State) (c : model.ClassExpression)
    (ran : rdf_mapping.object_cardinality triples kinds blank role s fuel = .ok (some (c, s'))) :
    ObjectRestrictionOk triples blank n1 p1 f1 s s' c := by
  rw [rdf_mapping.object_cardinality] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMinCardinality
      (by simp [slice_val, owlMinCardinality]) index findRun
    simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, naturalRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some n =>
      simp [take_correct, Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨[⟨.blank blank, owlMinCardinality, objectView t.object⟩], [], [], by simpa using grows1, fun rest => by
        simpa using TCE.min n role blank (f1 ++ rest) rest n1 _ p1 (roleOk rest) (node_natural_spec _ n naturalRun)⟩
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlMaxCardinality
        (by simp [slice_val, owlMaxCardinality]) index findRun1
      simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, naturalRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some n =>
        simp [take_correct, Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        exact ⟨[⟨.blank blank, owlMaxCardinality, objectView t.object⟩], [], [], by simpa using grows1, fun rest => by
          simpa using TCE.max n role blank (f1 ++ rest) rest n1 _ p1 (roleOk rest) (node_natural_spec _ n naturalRun)⟩
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => exact object_qualified_spec triples kinds fuel right blank role n1 p1 f1 roleOk s s' c ran
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlCardinality
          (by simp [slice_val, owlCardinality]) index findRun2
        simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, naturalRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some n =>
          simp [take_correct, Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          exact ⟨[⟨.blank blank, owlCardinality, objectView t.object⟩], [], [], by simpa using grows1, fun rest => by
            simpa using TCE.exact n role blank (f1 ++ rest) rest n1 _ p1 (roleOk rest)
              (node_natural_spec _ n naturalRun)⟩

theorem object_restriction_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (blank : rdf.BlankNode)
    (role : model.ObjectPropertyExpression) (n1 : Node) (p1 : List Pattern) (f1 : Supply)
    (roleOk : ∀ rest, TOPE role (f1 ++ rest) n1 p1 rest) (s s' : rdf_mapping.State) (c : model.ClassExpression)
    (ran : rdf_mapping.object_restriction triples kinds blank role s fuel = .ok (some (c, s'))) :
    ObjectRestrictionOk triples blank n1 p1 f1 s s' c := by
  rw [rdf_mapping.object_restriction] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlSomeValuesFrom
      (by simp [slice_val, owlSomeValuesFrom]) index findRun
    simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, classRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p =>
      obtain ⟨filler, s2⟩ := p
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨patterns, fresh, grows2, tce⟩ := right t.object _ s2 filler classRun
      exact ⟨[⟨.blank blank, owlSomeValuesFrom, objectView t.object⟩], patterns, fresh,
        by simpa using grows_trans grows1 grows2, fun rest => by
          simpa using TCE.some role filler blank (f1 ++ (fresh ++ rest)) (fresh ++ rest) rest n1 _ p1 patterns
            (roleOk _) (tce rest)⟩
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlAllValuesFrom
        (by simp [slice_val, owlAllValuesFrom]) index findRun1
      simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, classRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p =>
        obtain ⟨filler, s2⟩ := p
        simp [Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        obtain ⟨patterns, fresh, grows2, tce⟩ := right t.object _ s2 filler classRun
        exact ⟨[⟨.blank blank, owlAllValuesFrom, objectView t.object⟩], patterns, fresh,
          by simpa using grows_trans grows1 grows2, fun rest => by
            simpa using TCE.all role filler blank (f1 ++ (fresh ++ rest)) (fresh ++ rest) rest n1 _ p1 patterns
              (roleOk _) (tce rest)⟩
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlHasValue
          (by simp [slice_val, owlHasValue]) index findRun2
        simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, individualRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some value =>
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          rw [node_individual_spec _ value individualRun] at grows1
          exact ⟨[⟨.blank blank, owlHasValue, individualNode value⟩], [], [], by simpa using grows1, fun rest => by
            simpa using TCE.hasValue role value blank (f1 ++ rest) rest n1 p1 (roleOk rest)⟩
      | none =>
        simp only at ran
        obtain ⟨o3, findRun3, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => exact object_cardinality_spec triples kinds fuel right blank role n1 p1 f1 roleOk s s' c ran
        | some index =>
          obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlHasSelf
            (by simp [slice_val, owlHasSelf]) index findRun3
          simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
          obtain ⟨b, trueRun, ran⟩ := bind_eq_ok ran
          cases b with
          | false => simp at ran
          | true =>
            simp [Result.ok.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            rw [node_true_spec _ trueRun] at grows1
            exact ⟨[⟨.blank blank, owlHasSelf, trueNode⟩], [], [], by simpa using grows1, fun rest => by
              simpa using TCE.hasSelf role blank (f1 ++ rest) rest n1 p1 (roleOk rest)⟩

theorem restriction_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (blank : rdf.BlankNode) (s s' : rdf_mapping.State)
    (c : model.ClassExpression) (ran : rdf_mapping.restriction triples kinds blank s fuel = .ok (some (c, s'))) :
    ∃ patterns fresh, Grows triples.val s s' patterns fresh ∧
      ∀ rest, TCE c (blank :: (fresh ++ rest)) (.blank blank)
        (⟨.blank blank, rdfType, .iri owlRestriction⟩ :: patterns) rest := by
  rw [rdf_mapping.restriction] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlOnProperty
      (by simp [slice_val, owlOnProperty]) index findRun
    simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, kindRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some pk =>
      cases pk with
      | Annotation => simp at ran
      | Object =>
        simp only at ran
        obtain ⟨o2, roleRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran
        | some p =>
          obtain ⟨role, s2⟩ := p
          obtain ⟨p1, f1, grows2, tope⟩ := property_expression_spec triples t.object _ s2 role roleRun
          obtain ⟨head, tail, fresh, grows3, tce⟩ := object_restriction_spec triples kinds fuel right blank role
            (objectView t.object) p1 f1 tope s2 s' c ran
          have chain : Grows triples.val s s'
              (⟨.blank blank, owlOnProperty, objectView t.object⟩ :: (p1 ++ (head ++ tail))) (f1 ++ fresh) := by
            simpa using grows_trans (grows_trans grows1 grows2) grows3
          refine ⟨⟨.blank blank, owlOnProperty, objectView t.object⟩ :: (head ++ (p1 ++ tail)), f1 ++ fresh,
            grows_same chain ?_, fun rest => ?_⟩
          · intro x
            simp only [List.mem_cons, List.mem_append]
            tauto
          · simpa [restrictionHead, List.append_assoc] using tce rest
      | Data =>
        simp only at ran
        obtain ⟨o2, iriRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran
        | some iri =>
          simp only at ran
          obtain ⟨head, tail, fresh, grows2, tce⟩ := data_restriction_spec triples kinds blank ⟨iri⟩ _ s' fuel c ran
          have view := node_iri_spec t.object iri iriRun
          refine ⟨⟨.blank blank, owlOnProperty, objectView t.object⟩ :: (head ++ tail), fresh,
            by simpa using grows_trans grows1 grows2, fun rest => ?_⟩
          rw [view]
          simpa [restrictionHead] using tce rest

theorem class_members_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (out values : alloc.vec.Vec model.ClassExpression),
      rdf_mapping.class_members triples kinds firsts index s out fuel = .ok (some (values, s')) →
      ∃ news patterns fresh, values.val = out.val ++ news ∧ news.length = firsts.val.length - index.val ∧
        Grows triples.val s s' patterns fresh ∧
        ∀ rest, ∃ nodes, nodes = elementsFrom triples.val firsts.val index.val ∧
          TCEs news (fresh ++ rest) nodes patterns rest := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro s s' out values ran
    rw [rdf_mapping.class_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], [], by simp, by simp, grows_refl _ _,
      fun rest => ⟨[], by rw [elements_end _ _ _ (by omega)], .nil rest⟩⟩
  | succ n ih =>
    intro s s' out values ran
    rw [rdf_mapping.class_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts index more, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts index node more elementRun
      simp only at ran
      obtain ⟨o1, classRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some p =>
        obtain ⟨member, s1⟩ := p
        obtain ⟨p1, f1, grows, tce⟩ := right node s s1 member classRun
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out member room)
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance] at ran
          obtain ⟨news, patterns, fresh, split, count, grows', tces⟩ := ih next (by omega) s1 s' pushed values ran
          refine ⟨member :: news, p1 ++ patterns, f1 ++ fresh, by rw [split, contents]; simp,
            by simp only [List.length_cons]; omega, grows_trans grows grows', fun rest => ?_⟩
          obtain ⟨nodes, nodesIs, tail⟩ := tces rest
          refine ⟨elementNode triples.val firsts.val[index.val] :: nodes, by rw [elements_cons _ _ _ more, nodesIs,
            nextIndex], ?_⟩
          rw [List.append_assoc]
          have head := tce (fresh ++ rest)
          rw [view] at head
          exact .cons member news _ _ _ _ nodes p1 patterns head tail
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

theorem class_list2_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (node : rdf.Object) (s s' : rdf_mapping.State)
    (xs : model.AtLeastTwo model.ClassExpression)
    (ran : rdf_mapping.class_list2 triples kinds node s fuel = .ok (some (xs, s'))) :
    ∃ cells nodes patterns fresh, cells.length = (members2 xs).length ∧
      Grows triples.val s s' ((listOf cells nodes).2 ++ patterns) (cells ++ fresh) ∧
      (listOf cells nodes).1 = objectView node ∧ ∀ rest, TCEs (members2 xs) (fresh ++ rest) nodes patterns rest := by
  rw [rdf_mapping.class_list2] at ran
  obtain ⟨o, cellsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨firsts, s1⟩ := p
    obtain ⟨news, cells, split, lengths, grows, head⟩ := cells_spec triples fuel.val fuel node s s1 _ firsts rfl cellsRun
    simp at split
    by_cases two : 2 ≤ firsts.val.length
    · have twoU : alloc.vec.Vec.len firsts ≥ 2#usize := by scalar_tac
      have lookup0 := index_at firsts 0#usize (by simp; omega)
      have lookup1 := index_at firsts 1#usize (by simp; omega)
      simp [twoU, two, lookup0, lookup1] at ran
      obtain ⟨o1, elementRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some one =>
        simp only at ran
        obtain ⟨o2, firstRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran
        | some p1 =>
          obtain ⟨first, s2⟩ := p1
          obtain ⟨ps1, f1, grows1, tce1⟩ := right one s1 s2 first firstRun
          obtain ⟨o3, elementRun2, ran⟩ := bind_eq_ok ran
          cases o3 with
          | none => simp at ran
          | some two' =>
            simp only at ran
            obtain ⟨o4, secondRun, ran⟩ := bind_eq_ok ran
            cases o4 with
            | none => simp at ran
            | some p2 =>
              obtain ⟨second, s3⟩ := p2
              obtain ⟨ps2, f2, grows2, tce2⟩ := right two' s2 s3 second secondRun
              obtain ⟨o5, membersRun, ran⟩ := bind_eq_ok ran
              cases o5 with
              | none => simp at ran
              | some p3 =>
                obtain ⟨others, s4⟩ := p3
                simp [Result.ok.injEq] at ran
                obtain ⟨rfl, rfl⟩ := ran
                obtain ⟨news3, ps3, f3, restIs, count3, grows3, tces3⟩ := class_members_spec triples kinds fuel right
                  firsts 2#usize s3 s4 _ others membersRun
                simp at restIs
                simp only [show (2#usize).val = 2 from rfl] at count3 tces3
                have view0 := element_at triples firsts 0#usize one (by simp; omega) elementRun
                have view1 := element_at triples firsts 1#usize two' (by simp; omega) elementRun2
                simp only [show (0#usize).val = 0 from rfl] at view0
                simp only [show (1#usize).val = 1 from rfl] at view1
                have c0 : elementsFrom triples.val firsts.val 0 =
                    elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 :=
                  elements_cons triples.val firsts.val 0 (by omega)
                have c1 : elementsFrom triples.val firsts.val 1 =
                    elementNode triples.val firsts.val[1] :: elementsFrom triples.val firsts.val 2 :=
                  elements_cons triples.val firsts.val 1 (by omega)
                have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
                  simp [elementsFrom, split]
                refine ⟨cells, news.map (elementNode triples.val), ps1 ++ (ps2 ++ ps3), f1 ++ (f2 ++ f3), ?_, ?_,
                  head, fun rest => ?_⟩
                · simp only [members2, List.length_cons, restIs]
                  rw [lengths, ← split]
                  omega
                · simpa [List.append_assoc] using grows_trans (grows_trans (grows_trans grows grows1) grows2) grows3
                · obtain ⟨nodes, nodesIs, tail⟩ := tces3 rest
                  rw [nodesIs] at tail
                  rw [start, c0, c1]
                  simp only [members2, restIs, List.append_assoc]
                  have head1 := tce1 (f2 ++ (f3 ++ rest))
                  have head2 := tce2 (f3 ++ rest)
                  rw [view0] at head1
                  rw [view1] at head2
                  exact .cons first (second :: news3) _ _ _ _ _ ps1 (ps2 ++ ps3) head1
                    (.cons second news3 _ _ _ _ _ ps2 ps3 head2 tail)
    · have noneU : ¬ alloc.vec.Vec.len firsts ≥ 2#usize := by scalar_tac
      simp [noneU, two] at ran

theorem class_construct_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (right : ClassRight triples kinds fuel) (blank : rdf.BlankNode) (s s' : rdf_mapping.State)
    (c : model.ClassExpression) (ran : rdf_mapping.class_construct triples kinds blank s fuel = .ok (some (c, s'))) :
    ∃ patterns fresh, Grows triples.val s s' patterns fresh ∧
      ∀ rest, TCE c (blank :: (fresh ++ rest)) (.blank blank) (⟨.blank blank, rdfType, .iri owlClass⟩ :: patterns)
        rest := by
  rw [rdf_mapping.class_construct] at ran
  simp only [lift, bind_ok] at ran
  obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
  cases o with
  | some index =>
    obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlIntersectionOf
      (by simp [slice_val, owlIntersectionOf]) index findRun
    simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
    obtain ⟨o1, listRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p =>
      obtain ⟨members, s2⟩ := p
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨cells, nodes, patterns, fresh, lengths, grows2, head, tces⟩ := class_list2_spec triples kinds fuel right
        t.object _ s2 members listRun
      refine ⟨_ :: ((listOf cells nodes).2 ++ patterns), cells ++ fresh, by simpa using grows_trans grows1 grows2,
        fun rest => ?_⟩
      have tce := TCE.intersection members blank cells (fresh ++ rest) rest nodes patterns lengths (tces rest)
      rw [head] at tce
      simpa only [List.append_assoc] using tce
  | none =>
    simp only at ran
    obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
    cases o1 with
    | some index =>
      obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlUnionOf
        (by simp [slice_val, owlUnionOf]) index findRun1
      simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
      obtain ⟨o2, listRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p =>
        obtain ⟨members, s2⟩ := p
        simp [Result.ok.injEq] at ran
        obtain ⟨rfl, rfl⟩ := ran
        obtain ⟨cells, nodes, patterns, fresh, lengths, grows2, head, tces⟩ := class_list2_spec triples kinds fuel
          right t.object _ s2 members listRun
        refine ⟨_ :: ((listOf cells nodes).2 ++ patterns), cells ++ fresh, by simpa using grows_trans grows1 grows2,
          fun rest => ?_⟩
        have tce := TCE.union members blank cells (fresh ++ rest) rest nodes patterns lengths (tces rest)
        rw [head] at tce
        simpa only [List.append_assoc] using tce
    | none =>
      simp only at ran
      obtain ⟨o2, findRun2, ran⟩ := bind_eq_ok ran
      cases o2 with
      | some index =>
        obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlComplementOf
          (by simp [slice_val, owlComplementOf]) index findRun2
        simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
        obtain ⟨o3, innerRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some p =>
          obtain ⟨inner, s2⟩ := p
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          obtain ⟨patterns, fresh, grows2, tce⟩ := right t.object _ s2 inner innerRun
          exact ⟨_ :: patterns, fresh, by simpa using grows_trans grows1 grows2,
            fun rest => TCE.complement inner blank (fresh ++ rest) rest _ patterns (tce rest)⟩
      | none =>
        simp only at ran
        obtain ⟨o3, findRun3, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some index =>
          obtain ⟨t, lookup, grows1⟩ := found_take triples s blank _ owlOneOf
            (by simp [slice_val, owlOneOf]) index findRun3
          simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup, bind_ok] at ran
          obtain ⟨o4, listRun, ran⟩ := bind_eq_ok ran
          cases o4 with
          | none => simp at ran
          | some p =>
            obtain ⟨members, s2⟩ := p
            simp [Result.ok.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            obtain ⟨cells, lengths, grows2, head⟩ := individual_list1_spec triples t.object _ s2 fuel members listRun
            refine ⟨_ :: (listOf cells ((members1 members).map individualNode)).2, cells,
              by simpa using grows_trans grows1 grows2, fun rest => ?_⟩
            have tce := TCE.oneOf members blank cells rest lengths
            rw [head] at tce
            exact tce

theorem class_expression_step (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (fuel : Usize) (below : ∀ (i : Usize), i.val + 1 = fuel.val → ClassRight triples kinds i) :
    ClassRight triples kinds fuel := by
  intro node s s' c ran
  rw [rdf_mapping.class_expression.eq_def] at ran
  cases node with
  | Iri iri =>
    simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], grows_refl _ _, fun rest => by simpa [objectView, iriNode] using TCE.named ⟨⟨iri.spelling⟩⟩ rest⟩
  | Literal _ => simp at ran
  | Blank b =>
    by_cases positive : fuel > 0#usize
    · simp only [positive, ↓reduceIte, lift, bind_ok] at ran
      obtain ⟨fewer, back, fewerValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := fuel) (y := 1#usize) (by scalar_tac))
      have fewerIs : fewer.val + 1 = fuel.val := by
        have : fuel.val > 0 := by scalar_tac
        simp at fewerValue
        omega
      have right := below fewer fewerIs
      obtain ⟨o, findRun, ran⟩ := bind_eq_ok ran
      cases o with
      | some index =>
        obtain ⟨t, unused, subject, predicate, object⟩ := find_type_spec _ _ _ _ _ _ findRun
        simp only [take_correct, bind_ok] at ran
        obtain ⟨s2, recordRun, ran⟩ := bind_eq_ok ran
        simp only [back, bind_ok] at ran
        obtain ⟨patterns, fresh, grows, tce⟩ := restriction_spec triples kinds fewer right b s2 s' c ran
        have g1 := grows_take triples.val s index t ⟨.blank b, rdfType, .iri owlRestriction⟩ unused
          ⟨subject, predicate, by simpa [slice_val, owlRestriction] using object⟩
        have g2 := grows_record triples.val _ s2 b recordRun
        exact ⟨_ :: patterns, b :: fresh, by simpa using grows_trans (grows_trans g1 g2) grows,
          fun rest => by simpa [objectView] using tce rest⟩
      | none =>
        simp only at ran
        obtain ⟨o1, findRun1, ran⟩ := bind_eq_ok ran
        cases o1 with
        | none => simp at ran
        | some index =>
          obtain ⟨t, unused, subject, predicate, object⟩ := find_type_spec _ _ _ _ _ _ findRun1
          simp only [take_correct, bind_ok] at ran
          obtain ⟨s2, recordRun, ran⟩ := bind_eq_ok ran
          simp only [back, bind_ok] at ran
          obtain ⟨patterns, fresh, grows, tce⟩ := class_construct_spec triples kinds fewer right b s2 s' c ran
          have g1 := grows_take triples.val s index t ⟨.blank b, rdfType, .iri owlClass⟩ unused
            ⟨subject, predicate, by simpa [slice_val, owlClass] using object⟩
          have g2 := grows_record triples.val _ s2 b recordRun
          exact ⟨_ :: patterns, b :: fresh, by simpa using grows_trans (grows_trans g1 g2) grows,
            fun rest => by simpa [objectView] using tce rest⟩
    · simp [positive] at ran

theorem class_expression_right (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared) :
    ∀ (fuel : Usize), ClassRight triples kinds fuel := by
  have every : ∀ (n : Nat) (fuel : Usize), fuel.val = n → ClassRight triples kinds fuel := by
    intro n
    induction n with
    | zero => intro fuel same; exact class_expression_step triples kinds fuel (fun i h => by omega)
    | succ n ih => intro fuel same; exact class_expression_step triples kinds fuel (fun i h => ih i (by omega))
  exact fun fuel => every fuel.val fuel rfl

/-! ### Pairs, lists and keys of axioms -/

theorem main_lookup (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (t : rdf.Triple)
    (at_t : triples.val[index.val]? = some t) : triples.index_usize index = .ok t := by
  simp [alloc.vec.Vec.index_usize, at_t]

theorem topes_length {es : List model.ObjectPropertyExpression} {s : Supply} {ns : List Node} {ps : List Pattern}
    {s' : Supply} (h : TOPEs es s ns ps s') : es.length = ns.length := by
  induction h with
  | nil => rfl
  | cons => simp_all

theorem topes_nil {s : Supply} {ns : List Node} {ps : List Pattern} {s' : Supply} (h : TOPEs [] s ns ps s') :
    ns = [] ∧ ps = [] ∧ s' = s := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem class_pair_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s s' : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (first second : model.ClassExpression)
    (ran : rdf_mapping.class_pair triples kinds index s fuel = .ok (some (first, second, s'))) :
    ∃ p1 p2 f1 f2, Grows triples.val s s'
        (⟨subjectView t.subject, t.predicate.spelling.val, objectView t.object⟩ :: (p1 ++ p2)) (f1 ++ f2) ∧
      (∀ rest, TCE first (f1 ++ rest) (subjectView t.subject) p1 rest) ∧
      (∀ rest, TCE second (f2 ++ rest) (objectView t.object) p2 rest) := by
  rw [rdf_mapping.class_pair] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, nodeRun,
    bind_ok] at ran
  obtain ⟨o, firstRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨l, s2⟩ := p
    obtain ⟨o1, secondRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p1 =>
      obtain ⟨r, s3⟩ := p1
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl, rfl⟩ := ran
      obtain ⟨p1, f1, grows1, tce1⟩ := class_expression_right triples kinds fuel node _ s2 l firstRun
      obtain ⟨p2, f2, grows2, tce2⟩ := class_expression_right triples kinds fuel t.object s2 s3 r secondRun
      have g0 := grows_take triples.val s index t
        ⟨subjectView t.subject, t.predicate.spelling.val, objectView t.object⟩ unused ⟨rfl, rfl, rfl⟩
      refine ⟨p1, p2, f1, f2, by simpa using grows_trans (grows_trans g0 grows1) grows2, fun rest => ?_, tce2⟩
      rw [← view]
      exact tce1 rest

theorem property_pair_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (s s' : rdf_mapping.State)
    (t : rdf.Triple) (at_t : triples.val[index.val]? = some t) (first second : model.ObjectPropertyExpression)
    (ran : rdf_mapping.property_pair triples index s = .ok (some (first, second, s'))) :
    ∃ p1 p2 f1 f2, Grows triples.val s s' (p1 ++ p2) (f1 ++ f2) ∧
      (∀ rest, TOPE first (f1 ++ rest) (subjectView t.subject) p1 rest) ∧
      (∀ rest, TOPE second (f2 ++ rest) (objectView t.object) p2 rest) := by
  rw [rdf_mapping.property_pair] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t at_t, nodeRun, bind_ok] at ran
  obtain ⟨o, firstRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨l, s1⟩ := p
    obtain ⟨o1, secondRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p1 =>
      obtain ⟨r, s2⟩ := p1
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl, rfl⟩ := ran
      obtain ⟨p1, f1, grows1, tope1⟩ := property_expression_spec triples node _ s1 l firstRun
      obtain ⟨p2, f2, grows2, tope2⟩ := property_expression_spec triples t.object s1 s2 r secondRun
      exact ⟨p1, p2, f1, f2, grows_trans grows1 grows2, fun rest => by rw [← view]; exact tope1 rest, tope2⟩

theorem data_pair_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (t : rdf.Triple)
    (at_t : triples.val[index.val]? = some t) (first second : model.DataProperty)
    (ran : rdf_mapping.data_pair triples index = .ok (some (first, second))) :
    iriNode first.iri = subjectView t.subject ∧ iriNode second.iri = objectView t.object := by
  rw [rdf_mapping.data_pair] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t at_t, nodeRun, bind_ok] at ran
  obtain ⟨o, firstRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some l =>
    obtain ⟨o1, secondRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some r =>
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨by rw [← view]; exact (node_iri_spec node l firstRun).symm, (node_iri_spec t.object r secondRun).symm⟩

theorem individual_pair_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (t : rdf.Triple)
    (at_t : triples.val[index.val]? = some t) (first second : model.Individual)
    (ran : rdf_mapping.individual_pair triples index = .ok (some (first, second))) :
    individualNode first = subjectView t.subject ∧ individualNode second = objectView t.object := by
  rw [rdf_mapping.individual_pair] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t at_t, nodeRun, bind_ok] at ran
  obtain ⟨o, firstRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some l =>
    obtain ⟨o1, secondRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some r =>
      simp [Result.ok.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨by rw [← view]; exact (node_individual_spec node l firstRun).symm,
        (node_individual_spec t.object r secondRun).symm⟩

theorem property_element_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (firsts : alloc.vec.Vec Usize) (k : Usize) (s s' : rdf_mapping.State) (role : model.ObjectPropertyExpression)
    (ran : rdf_mapping.property_element triples kinds firsts k s = .ok (some (role, s'))) :
    ∃ (inside : k.val < firsts.val.length) (patterns : List Pattern) (fresh : List rdf.BlankNode),
      Grows triples.val s s' patterns fresh ∧
      ∀ rest, TOPE role (fresh ++ rest) (elementNode triples.val firsts.val[k.val]) patterns rest := by
  rw [rdf_mapping.property_element] at ran
  by_cases inside : k.val < firsts.val.length
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts k inside, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts k node inside elementRun
      simp only at ran
      obtain ⟨o1, kindRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some pk =>
        cases pk with
        | Data => simp at ran
        | Annotation => simp at ran
        | Object =>
          obtain ⟨patterns, fresh, grows, tope⟩ := property_expression_spec triples node s s' role ran
          exact ⟨inside, patterns, fresh, grows, fun rest => by rw [← view]; exact tope rest⟩
  · simp [UScalar.lt_equiv, inside] at ran

theorem property_members_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (out values : alloc.vec.Vec model.ObjectPropertyExpression),
      rdf_mapping.property_members triples kinds firsts index s out = .ok (some (values, s')) →
      ∃ news patterns fresh, values.val = out.val ++ news ∧ news.length = firsts.val.length - index.val ∧
        Grows triples.val s s' patterns fresh ∧
        ∀ rest, ∃ nodes, nodes = elementsFrom triples.val firsts.val index.val ∧
          TOPEs news (fresh ++ rest) nodes patterns rest := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro s s' out values ran
    rw [rdf_mapping.property_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], [], by simp, by simp, grows_refl _ _,
      fun rest => ⟨[], by rw [elements_end _ _ _ (by omega)], .nil rest⟩⟩
  | succ n ih =>
    intro s s' out values ran
    rw [rdf_mapping.property_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts index more, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts index node more elementRun
      simp only at ran
      obtain ⟨o1, kindRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some pk =>
        cases pk with
        | Data => simp at ran
        | Annotation => simp at ran
        | Object =>
          simp only at ran
          obtain ⟨o2, roleRun, ran⟩ := bind_eq_ok ran
          cases o2 with
          | none => simp at ran
          | some p =>
            obtain ⟨member, s1⟩ := p
            obtain ⟨p1, f1, grows, tope⟩ := property_expression_spec triples node s s1 member roleRun
            by_cases room : out.val.length < Usize.max
            · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out member room)
              obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
                (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
              have nextIndex : next.val = index.val + 1 := by simpa using nextValue
              simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance] at ran
              obtain ⟨news, patterns, fresh, split, count, grows', topes⟩ := ih next (by omega) s1 s' pushed values ran
              refine ⟨member :: news, p1 ++ patterns, f1 ++ fresh, by rw [split, contents]; simp,
                by simp only [List.length_cons]; omega, grows_trans grows grows', fun rest => ?_⟩
              obtain ⟨nodes, nodesIs, tail⟩ := topes rest
              refine ⟨elementNode triples.val firsts.val[index.val] :: nodes, by rw [elements_cons _ _ _ more,
                nodesIs, nextIndex], ?_⟩
              rw [List.append_assoc]
              have head := tope (fresh ++ rest)
              rw [view] at head
              exact .cons member news _ _ _ _ nodes p1 patterns head tail
            · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

theorem property_list2_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (node : rdf.Object) (s s' : rdf_mapping.State) (fuel : Usize)
    (xs : model.AtLeastTwo model.ObjectPropertyExpression)
    (ran : rdf_mapping.property_list2 triples kinds node s fuel = .ok (some (xs, s'))) :
    ∃ cells nodes patterns fresh, cells.length = (members2 xs).length ∧
      Grows triples.val s s' ((listOf cells nodes).2 ++ patterns) (cells ++ fresh) ∧
      (listOf cells nodes).1 = objectView node ∧ ∀ rest, TOPEs (members2 xs) (fresh ++ rest) nodes patterns rest := by
  rw [rdf_mapping.property_list2] at ran
  obtain ⟨o, cellsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨firsts, s1⟩ := p
    obtain ⟨news, cells, split, lengths, grows, head⟩ := cells_spec triples fuel.val fuel node s s1 _ firsts rfl cellsRun
    simp at split
    obtain ⟨o1, firstRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some p1 =>
      obtain ⟨first, s2⟩ := p1
      obtain ⟨inside0, ps1, f1, grows1, tope1⟩ := property_element_spec triples kinds firsts 0#usize s1 s2 first firstRun
      obtain ⟨o2, secondRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p2 =>
        obtain ⟨second, s3⟩ := p2
        obtain ⟨inside1, ps2, f2, grows2, tope2⟩ := property_element_spec triples kinds firsts 1#usize s2 s3 second
          secondRun
        obtain ⟨o3, membersRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some p3 =>
          obtain ⟨others, s4⟩ := p3
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          obtain ⟨news3, ps3, f3, restIs, count3, grows3, topes3⟩ := property_members_spec triples kinds firsts
            2#usize s3 s4 _ others membersRun
          simp at restIs
          simp only [show (0#usize).val = 0 from rfl] at inside0 tope1
          simp only [show (1#usize).val = 1 from rfl] at inside1 tope2
          simp only [show (2#usize).val = 2 from rfl] at count3 topes3
          have c0 : elementsFrom triples.val firsts.val 0 =
              elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 :=
            elements_cons triples.val firsts.val 0 (by omega)
          have c1 : elementsFrom triples.val firsts.val 1 =
              elementNode triples.val firsts.val[1] :: elementsFrom triples.val firsts.val 2 :=
            elements_cons triples.val firsts.val 1 (by omega)
          have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
            simp [elementsFrom, split]
          refine ⟨cells, news.map (elementNode triples.val), ps1 ++ (ps2 ++ ps3), f1 ++ (f2 ++ f3), ?_, ?_, head,
            fun rest => ?_⟩
          · simp only [members2, List.length_cons, restIs]
            rw [lengths, ← split]
            omega
          · simpa [List.append_assoc] using grows_trans (grows_trans (grows_trans grows grows1) grows2) grows3
          · obtain ⟨nodes, nodesIs, tail⟩ := topes3 rest
            rw [nodesIs] at tail
            rw [start, c0, c1]
            simp only [members2, restIs, List.append_assoc]
            exact .cons first (second :: news3) _ _ _ _ _ ps1 (ps2 ++ ps3) (tope1 _)
              (.cons second news3 _ _ _ _ _ ps2 ps3 (tope2 _) tail)

theorem data_element_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (firsts : alloc.vec.Vec Usize) (k : Usize) (d : model.DataProperty)
    (ran : rdf_mapping.data_element triples kinds firsts k = .ok (some d)) :
    ∃ (inside : k.val < firsts.val.length), iriNode d.iri = elementNode triples.val firsts.val[k.val] := by
  rw [rdf_mapping.data_element] at ran
  by_cases inside : k.val < firsts.val.length
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts k inside, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts k node inside elementRun
      simp only at ran
      obtain ⟨o1, kindRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some pk =>
        cases pk with
        | Object => simp at ran
        | Annotation => simp at ran
        | Data =>
          simp only at ran
          obtain ⟨o2, iriRun, ran⟩ := bind_eq_ok ran
          cases o2 with
          | none => simp at ran
          | some iri =>
            simp [Result.ok.injEq] at ran
            subst ran
            exact ⟨inside, by rw [← view]; exact (node_iri_spec node iri iriRun).symm⟩
  · simp [UScalar.lt_equiv, inside] at ran

theorem data_members_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (out values : alloc.vec.Vec model.DataProperty),
      rdf_mapping.data_members triples kinds firsts index out = .ok (some values) →
      ∃ news, values.val = out.val ++ news ∧
        news.map (iriNode ·.iri) = elementsFrom triples.val firsts.val index.val := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro out values ran
    rw [rdf_mapping.data_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    exact ⟨[], by simp, by rw [elements_end _ _ _ (by omega)]; rfl⟩
  | succ n ih =>
    intro out values ran
    rw [rdf_mapping.data_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts index more, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts index node more elementRun
      simp only at ran
      obtain ⟨o1, kindRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some pk =>
        cases pk with
        | Object => simp at ran
        | Annotation => simp at ran
        | Data =>
          simp only at ran
          obtain ⟨o2, iriRun, ran⟩ := bind_eq_ok ran
          cases o2 with
          | none => simp at ran
          | some iri =>
            simp only at ran
            by_cases room : out.val.length < Usize.max
            · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
                (alloc.vec.Vec.push_spec out ({ iri } : model.DataProperty) room)
              obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
                (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
              have nextIndex : next.val = index.val + 1 := by simpa using nextValue
              simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, ↓reduceIte, push, advance,
                bind_ok] at ran
              obtain ⟨news, split, all⟩ := ih next (by omega) pushed values ran
              refine ⟨{ iri } :: news, by rw [split, contents]; simp, ?_⟩
              rw [nextIndex] at all
              have e : elementNode triples.val firsts.val[index.val] = iriNode iri := by
                rw [← node_iri_spec node iri iriRun]
                exact view.symm
              rw [elements_cons _ _ _ more, e, ← all]
              rfl
            · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

theorem data_list2_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (node : rdf.Object) (s s' : rdf_mapping.State) (fuel : Usize) (xs : model.AtLeastTwo model.DataProperty)
    (ran : rdf_mapping.data_list2 triples kinds node s fuel = .ok (some (xs, s'))) :
    ∃ cells, cells.length = (members2 xs).length ∧
      Grows triples.val s s' (listOf cells ((members2 xs).map (iriNode ·.iri))).2 cells ∧
      (listOf cells ((members2 xs).map (iriNode ·.iri))).1 = objectView node := by
  rw [rdf_mapping.data_list2] at ran
  obtain ⟨o, cellsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨firsts, s1⟩ := p
    obtain ⟨news, cells, split, lengths, grows, head⟩ := cells_spec triples fuel.val fuel node s s1 _ firsts rfl cellsRun
    simp at split
    obtain ⟨o1, firstRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran
    | some first =>
      obtain ⟨inside0, view0⟩ := data_element_spec triples kinds firsts 0#usize first firstRun
      simp only at ran
      obtain ⟨o2, secondRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some second =>
        obtain ⟨inside1, view1⟩ := data_element_spec triples kinds firsts 1#usize second secondRun
        simp only at ran
        obtain ⟨o3, membersRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some others =>
          simp [Result.ok.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          obtain ⟨news3, restIs, all⟩ := data_members_spec triples kinds firsts 2#usize _ others membersRun
          simp at restIs
          simp only [show (0#usize).val = 0 from rfl] at inside0 view0
          simp only [show (1#usize).val = 1 from rfl] at inside1 view1
          simp only [show (2#usize).val = 2 from rfl] at all
          have c0 : elementsFrom triples.val firsts.val 0 =
              elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 :=
            elements_cons triples.val firsts.val 0 (by omega)
          have c1 : elementsFrom triples.val firsts.val 1 =
              elementNode triples.val firsts.val[1] :: elementsFrom triples.val firsts.val 2 :=
            elements_cons triples.val firsts.val 1 (by omega)
          have e0 : elementNode triples.val firsts.val[0] = iriNode first.iri := view0.symm
          have e1 : elementNode triples.val firsts.val[1] = iriNode second.iri := view1.symm
          have whole : (members2 (⟨first, second, others⟩ : model.AtLeastTwo model.DataProperty)).map
              (iriNode ·.iri) = news.map (elementNode triples.val) := by
            have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
              simp [elementsFrom, split]
            rw [start, c0, c1, e0, e1, ← all]
            simp [members2, restIs]
          have count : news3.length = firsts.val.length - 2 := by
            have := congrArg List.length all
            simpa [elementsFrom] using this
          refine ⟨cells, ?_, by rw [whole]; exact grows, by rw [whole]; exact head⟩
          simp only [members2, List.length_cons, restIs]
          rw [lengths, ← split]
          omega

theorem individual_list2_spec (triples : alloc.vec.Vec rdf.Triple) (node : rdf.Object) (s s' : rdf_mapping.State)
    (fuel : Usize) (xs : model.AtLeastTwo model.Individual)
    (ran : rdf_mapping.individual_list2 triples node s fuel = .ok (some (xs, s'))) :
    ∃ cells, cells.length = (members2 xs).length ∧
      Grows triples.val s s' (listOf cells ((members2 xs).map individualNode)).2 cells ∧
      (listOf cells ((members2 xs).map individualNode)).1 = objectView node := by
  rw [rdf_mapping.individual_list2] at ran
  obtain ⟨o, cellsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨firsts, s1⟩ := p
    obtain ⟨news, cells, split, lengths, grows, head⟩ := cells_spec triples fuel.val fuel node s s1 _ firsts rfl cellsRun
    simp at split
    by_cases two : 2 ≤ firsts.val.length
    · have twoU : alloc.vec.Vec.len firsts ≥ 2#usize := by scalar_tac
      have lookup0 := index_at firsts 0#usize (by simp; omega)
      have lookup1 := index_at firsts 1#usize (by simp; omega)
      simp [twoU, two, lookup0, lookup1] at ran
      obtain ⟨o1, elementRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some one =>
        simp only at ran
        obtain ⟨o2, firstRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran
        | some first =>
          simp only at ran
          obtain ⟨o3, elementRun2, ran⟩ := bind_eq_ok ran
          cases o3 with
          | none => simp at ran
          | some two' =>
            simp only at ran
            obtain ⟨o4, secondRun, ran⟩ := bind_eq_ok ran
            cases o4 with
            | none => simp at ran
            | some second =>
              simp only at ran
              obtain ⟨o5, membersRun, ran⟩ := bind_eq_ok ran
              cases o5 with
              | none => simp at ran
              | some others =>
                simp only [Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
                obtain ⟨rfl, rfl⟩ := ran
                obtain ⟨news3, restIs, all⟩ := individual_members_spec triples firsts 2#usize _ others membersRun
                simp at restIs
                simp only [show (2#usize).val = 2 from rfl] at all
                have view0 := element_at triples firsts 0#usize one (by simp; omega) elementRun
                have view1 := element_at triples firsts 1#usize two' (by simp; omega) elementRun2
                simp only [show (0#usize).val = 0 from rfl] at view0
                simp only [show (1#usize).val = 1 from rfl] at view1
                have c0 : elementsFrom triples.val firsts.val 0 =
                    elementNode triples.val firsts.val[0] :: elementsFrom triples.val firsts.val 1 :=
                  elements_cons triples.val firsts.val 0 (by omega)
                have c1 : elementsFrom triples.val firsts.val 1 =
                    elementNode triples.val firsts.val[1] :: elementsFrom triples.val firsts.val 2 :=
                  elements_cons triples.val firsts.val 1 (by omega)
                have e0 : elementNode triples.val firsts.val[0] = individualNode first := by
                  rw [← node_individual_spec one first firstRun]
                  exact view0.symm
                have e1 : elementNode triples.val firsts.val[1] = individualNode second := by
                  rw [← node_individual_spec two' second secondRun]
                  exact view1.symm
                have whole : (members2 (⟨first, second, others⟩ : model.AtLeastTwo model.Individual)).map
                    individualNode = news.map (elementNode triples.val) := by
                  have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
                    simp [elementsFrom, split]
                  rw [start, c0, c1, e0, e1, ← all]
                  simp [members2, restIs]
                have count : news3.length = firsts.val.length - 2 := by
                  have := congrArg List.length all
                  simpa [elementsFrom] using this
                refine ⟨cells, ?_, by rw [whole]; exact grows, by rw [whole]; exact head⟩
                simp only [members2, List.length_cons, restIs]
                rw [lengths, ← split]
                omega
    · have noneU : ¬ alloc.vec.Vec.len firsts ≥ 2#usize := by scalar_tac
      simp [noneU, two] at ran

theorem key_members_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (firsts : alloc.vec.Vec Usize) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (objs objs' : alloc.vec.Vec model.ObjectPropertyExpression)
      (datas datas' : alloc.vec.Vec model.DataProperty),
      rdf_mapping.key_members triples kinds firsts index s objs datas = .ok (some (objs', datas', s')) →
      ∃ newObjs newDatas nodes patterns fresh, objs'.val = objs.val ++ newObjs ∧
        datas'.val = datas.val ++ newDatas ∧ (datas.val ≠ [] → newObjs = []) ∧
        Grows triples.val s s' patterns fresh ∧
        nodes ++ newDatas.map (iriNode ·.iri) = elementsFrom triples.val firsts.val index.val ∧
        ∀ rest, TOPEs newObjs (fresh ++ rest) nodes patterns rest := by
  intro index
  induction h : firsts.val.length - index.val generalizing index with
  | zero =>
    intro s s' objs objs' datas datas' ran
    rw [rdf_mapping.key_members] at ran
    have done : ¬ index.val < firsts.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl, rfl⟩ := ran
    exact ⟨[], [], [], [], [], by simp, by simp, fun _ => rfl, grows_refl _ _,
      by rw [elements_end _ _ _ (by omega)]; rfl, fun rest => .nil rest⟩
  | succ n ih =>
    intro s s' objs objs' datas datas' ran
    rw [rdf_mapping.key_members] at ran
    have more : index.val < firsts.val.length := by omega
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      index_at firsts index more, bind_ok] at ran
    obtain ⟨o, elementRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some node =>
      have view := element_at triples firsts index node more elementRun
      simp only at ran
      obtain ⟨o1, kindRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran
      | some pk =>
        cases pk with
        | Annotation => simp at ran
        | Object =>
          by_cases empty : datas.val.length = 0
          · have emptyU : alloc.vec.Vec.len datas = 0#usize := by scalar_tac
            simp only [emptyU, ↓reduceIte] at ran
            obtain ⟨o2, roleRun, ran⟩ := bind_eq_ok ran
            cases o2 with
            | none => simp at ran
            | some p =>
              obtain ⟨member, s1⟩ := p
              obtain ⟨p1, f1, grows, tope⟩ := property_expression_spec triples node s s1 member roleRun
              by_cases room : objs.val.length < Usize.max
              · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec objs member room)
                obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
                  (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
                have nextIndex : next.val = index.val + 1 := by simpa using nextValue
                simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance] at ran
                obtain ⟨newObjs, newDatas, nodes, patterns, fresh, splitO, splitD, order, grows', joined, topes⟩ :=
                  ih next (by omega) s1 s' pushed objs' datas datas' ran
                have datasNil : datas.val = [] := List.eq_nil_of_length_eq_zero empty
                refine ⟨member :: newObjs, newDatas, elementNode triples.val firsts.val[index.val] :: nodes,
                  p1 ++ patterns, f1 ++ fresh, by rw [splitO, contents]; simp, splitD,
                  fun nonempty => absurd datasNil nonempty, grows_trans grows grows', ?_, fun rest => ?_⟩
                · rw [nextIndex] at joined
                  rw [elements_cons _ _ _ more, ← joined, List.cons_append]
                · rw [List.append_assoc]
                  have head := tope (fresh ++ rest)
                  rw [view] at head
                  exact .cons member newObjs _ _ _ _ nodes p1 patterns head (topes rest)
              · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran
          · have nonzero : ¬ alloc.vec.Vec.len datas = 0#usize := by scalar_tac
            simp [nonzero] at ran
        | Data =>
          simp only at ran
          obtain ⟨o2, iriRun, ran⟩ := bind_eq_ok ran
          cases o2 with
          | none => simp at ran
          | some iri =>
            simp only at ran
            by_cases room : datas.val.length < Usize.max
            · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
                (alloc.vec.Vec.push_spec datas ({ iri } : model.DataProperty) room)
              obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
                (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
              have nextIndex : next.val = index.val + 1 := by simpa using nextValue
              simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance] at ran
              obtain ⟨newObjs, newDatas, nodes, patterns, fresh, splitO, splitD, order, grows', joined, topes⟩ :=
                ih next (by omega) s s' objs objs' pushed datas' ran
              have nonempty : pushed.val ≠ [] := by rw [contents]; simp
              have objsNil := order nonempty
              subst objsNil
              obtain ⟨rfl, rfl, freshNil⟩ := topes_nil (topes [])
              have freshIs : fresh = [] := by simpa using freshNil
              subst freshIs
              refine ⟨[], { iri } :: newDatas, [], [], [], by simpa using splitO, by rw [splitD, contents]; simp,
                fun _ => rfl, grows', ?_, fun rest => .nil rest⟩
              rw [nextIndex] at joined
              have e : elementNode triples.val firsts.val[index.val] = iriNode iri := by
                rw [← node_iri_spec node iri iriRun]
                exact view.symm
              rw [elements_cons _ _ _ more, e, ← joined]
              rfl
            · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran

theorem annotation_value_spec (node : rdf.Object) (value : model.AnnotationValue)
    (ran : rdf_mapping.annotation_value node = .ok (some value)) : AnnotationValueNode value (objectView node) := by
  rw [rdf_mapping.annotation_value.eq_def] at ran
  cases node with
  | Iri iri =>
    simp only [iri_of_identity, bind_ok, Result.ok.injEq, Option.some.injEq] at ran
    subst ran
    exact .iri ⟨iri.spelling⟩
  | Blank b =>
    simp only [Rowl.Nnf.copy_bytes_identity, bind_ok, Result.ok.injEq, Option.some.injEq] at ran
    subst ran
    exact .anonymous _
  | Literal literal =>
    simp only at ran
    obtain ⟨o, literalRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran
    | some v =>
      simp only [Result.ok.injEq, Option.some.injEq] at ran
      subst ran
      exact .literal v _ (literal_of_spec literal v literalRun)

theorem annotation_subject_spec (subject : rdf.Subject) (value : model.AnnotationSubject)
    (ran : rdf_mapping.annotation_subject subject = .ok value) : annotationSubjectNode value = subjectView subject := by
  rw [rdf_mapping.annotation_subject.eq_def] at ran
  cases subject with
  | Iri iri =>
    simp only [iri_of_identity, bind_ok, Result.ok.injEq] at ran
    subst ran
    rfl
  | Blank b =>
    simp only [Rowl.Nnf.copy_bytes_identity, bind_ok, Result.ok.injEq] at ran
    subst ran
    rfl

/-! ### Axiom readers -/

/-- What an axiom reader returns is right: a skip reads nothing, and an axiom
    comes with the triples it read and the blank nodes it allocated. -/
def ReadOk (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) : rdf_mapping.Read → Prop
  | .Skip s' => Grows triples.val s s' [] []
  | .Found a s' => ∃ patterns fresh, Grows triples.val s s' patterns fresh ∧
      ∀ rest, TAxiom a (fresh ++ rest) patterns rest
  | .Fail => True

/-- The main triple of an axiom, used. -/
theorem take_main (triples : alloc.vec.Vec rdf.Triple) (s : rdf_mapping.State) (index : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) :
    Grows triples.val s { s with used := s.used.set index true }
      [⟨subjectView t.subject, t.predicate.spelling.val, objectView t.object⟩] [] :=
  grows_take triples.val s index t _ unused ⟨rfl, rfl, rfl⟩

theorem sub_class_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (predicate : t.predicate.spelling.val = rdfsSubClassOf)
    (r : rdf_mapping.Read) (ran : rdf_mapping.sub_class triples kinds index s fuel = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.sub_class] at ran
  obtain ⟨o, pairRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨c1, c2, s'⟩ := p
    simp at ran
    subst ran
    obtain ⟨p1, p2, f1, f2, grows, tce1, tce2⟩ := class_pair_spec triples kinds index s s' fuel t unused c1 c2 pairRun
    rw [predicate] at grows
    dsimp only [ReadOk]
    exact ⟨_, f1 ++ f2, grows, fun rest => by
      simpa using TAxiom.subClassOf c1 c2 (f1 ++ (f2 ++ rest)) (f2 ++ rest) rest _ _ p1 p2 (tce1 _) (tce2 rest)⟩

theorem equivalent_class_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (predicate : t.predicate.spelling.val = owlEquivalentClass)
    (r : rdf_mapping.Read) (ran : rdf_mapping.equivalent_class triples kinds index s fuel = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.equivalent_class] at ran
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, bind_ok] at ran
  obtain ⟨b, datatypeRun, ran⟩ := bind_eq_ok ran
  cases b with
  | true =>
    simp only [↓reduceIte, take_correct, bind_ok] at ran
    cases subject : t.subject with
    | Blank _ => simp [subject] at ran; subst ran; trivial
    | Iri iri =>
      simp only [subject] at ran
      obtain ⟨o, rangeRun, ran⟩ := bind_eq_ok ran
      cases o with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨range, s2⟩ := p
        simp [iri_of_identity] at ran
        subst ran
        obtain ⟨patterns, fresh, grows, tdr⟩ := data_range_right triples kinds fuel t.object _ s2 range rangeRun
        have g0 := take_main triples s index t unused
        rw [predicate, subject] at g0
        dsimp only [ReadOk]
        refine ⟨⟨.iri iri.spelling.val, owlEquivalentClass, objectView t.object⟩ :: patterns, fresh,
          by simpa [subjectView] using grows_trans g0 grows, fun rest => ?_⟩
        exact TAxiom.datatypeDefinition ⟨⟨iri.spelling⟩⟩ range (fresh ++ rest) rest _ patterns (tdr rest)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at ran
    obtain ⟨o, pairRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran; subst ran; trivial
    | some p =>
      obtain ⟨c1, c2, s'⟩ := p
      simp [rdf_mapping.two] at ran
      subst ran
      obtain ⟨p1, p2, f1, f2, grows, tce1, tce2⟩ := class_pair_spec triples kinds index s s' fuel t unused c1 c2
        pairRun
      rw [predicate] at grows
      dsimp only [ReadOk]
      refine ⟨_, f1 ++ f2, grows, fun rest => ?_⟩
      have tces : TCEs [c1, c2] (f1 ++ (f2 ++ rest)) [subjectView t.subject, objectView t.object]
          (p1 ++ (p2 ++ [])) rest :=
        .cons c1 [c2] _ _ _ _ _ p1 (p2 ++ []) (tce1 _) (.cons c2 [] _ _ _ _ _ p2 [] (tce2 rest) (.nil rest))
      simpa [chainOf] using TAxiom.equivalentClasses ⟨c1, c2, alloc.vec.Vec.new _⟩ _ _ _ _ tces

theorem disjoint_class_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (predicate : t.predicate.spelling.val = owlDisjointWith)
    (r : rdf_mapping.Read) (ran : rdf_mapping.disjoint_class triples kinds index s fuel = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.disjoint_class] at ran
  obtain ⟨o, pairRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨c1, c2, s'⟩ := p
    simp [rdf_mapping.two] at ran
    subst ran
    obtain ⟨p1, p2, f1, f2, grows, tce1, tce2⟩ := class_pair_spec triples kinds index s s' fuel t unused c1 c2 pairRun
    rw [predicate] at grows
    dsimp only [ReadOk]
    exact ⟨_, f1 ++ f2, grows, fun rest => by
      simpa using TAxiom.disjointClasses c1 c2 (f1 ++ (f2 ++ rest)) (f2 ++ rest) rest _ _ p1 p2 (tce1 _) (tce2 rest)⟩

theorem disjoint_union_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (predicate : t.predicate.spelling.val = owlDisjointUnionOf)
    (r : rdf_mapping.Read) (ran : rdf_mapping.disjoint_union triples kinds index s fuel = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.disjoint_union] at ran
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, bind_ok] at ran
  cases subject : t.subject with
  | Blank _ => simp [subject] at ran; subst ran; trivial
  | Iri iri =>
    simp only [subject, take_correct, bind_ok] at ran
    obtain ⟨o, listRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran; subst ran; trivial
    | some p =>
      obtain ⟨members, s2⟩ := p
      simp [iri_of_identity] at ran
      subst ran
      obtain ⟨cells, nodes, patterns, fresh, lengths, grows, head, tces⟩ := class_list2_spec triples kinds fuel
        (class_expression_right triples kinds fuel) t.object _ s2 members listRun
      have g0 := take_main triples s index t unused
      rw [predicate, subject] at g0
      dsimp only [ReadOk]
      refine ⟨⟨.iri iri.spelling.val, owlDisjointUnionOf, objectView t.object⟩ :: ((listOf cells nodes).2 ++ patterns),
        cells ++ fresh, by simpa [subjectView] using grows_trans g0 grows, fun rest => ?_⟩
      have statement := TAxiom.disjointUnion ⟨⟨iri.spelling⟩⟩ members cells (fresh ++ rest) rest nodes patterns lengths
        (tces rest)
      rw [head] at statement
      simpa only [List.append_assoc, iriNode] using statement

theorem sub_property_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (predicate : t.predicate.spelling.val = rdfsSubPropertyOf) (r : rdf_mapping.Read)
    (ran : rdf_mapping.sub_property triples kinds index s = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.sub_property] at ran
  simp only [take_correct, bind_ok] at ran
  have g0 := take_main triples s index t unused
  rw [predicate] at g0
  obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some pk =>
    cases pk with
    | Object =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨sub, sup, s2⟩ := p
        simp at ran
        subst ran
        obtain ⟨p1, p2, f1, f2, grows, tope1, tope2⟩ := property_pair_spec triples index _ s2 t unused.1 sub sup
          pairRun
        dsimp only [ReadOk]
        refine ⟨⟨subjectView t.subject, rdfsSubPropertyOf, objectView t.object⟩ :: (p1 ++ p2), f1 ++ f2,
          by simpa using grows_trans g0 grows, fun rest => ?_⟩
        simpa using TAxiom.subObjectProperty sub sup (f1 ++ (f2 ++ rest)) (f2 ++ rest) rest _ _ p1 p2 (tope1 _)
          (tope2 rest)
    | Data =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨sub, sup⟩ := p
        simp at ran
        subst ran
        obtain ⟨v1, v2⟩ := data_pair_spec triples index t unused.1 sub sup pairRun
        rw [← v1, ← v2] at g0
        dsimp only [ReadOk]
        exact ⟨_, [], g0, fun rest => TAxiom.subDataProperty sub sup rest⟩
    | Annotation =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨sub, sup⟩ := p
        simp at ran
        subst ran
        obtain ⟨v1, v2⟩ := data_pair_spec triples index t unused.1 sub sup pairRun
        rw [← v1, ← v2] at g0
        dsimp only [ReadOk]
        exact ⟨_, [], g0, fun rest => TAxiom.subAnnotationProperty ⟨sub.iri⟩ ⟨sup.iri⟩ rest⟩

theorem property_chain_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t)
    (predicate : t.predicate.spelling.val = owlPropertyChainAxiom) (r : rdf_mapping.Read)
    (ran : rdf_mapping.property_chain triples kinds index s fuel = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.property_chain] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, nodeRun,
    bind_ok] at ran
  obtain ⟨o, supRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨sup, s2⟩ := p
    obtain ⟨o1, chainRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran; subst ran; trivial
    | some p1 =>
      obtain ⟨chain, s3⟩ := p1
      simp at ran
      subst ran
      obtain ⟨q, f1, grows1, tope⟩ := property_expression_spec triples node _ s2 sup supRun
      obtain ⟨cells, nodes, ps, f2, lengths, grows2, head, topes⟩ := property_list2_spec triples kinds t.object s2 s3
        fuel chain chainRun
      have g0 := take_main triples s index t unused
      rw [predicate] at g0
      have whole : Grows triples.val s s3
          (⟨subjectView t.subject, owlPropertyChainAxiom, objectView t.object⟩ ::
            (q ++ ((listOf cells nodes).2 ++ ps))) (f1 ++ (cells ++ f2)) := by
        simpa using grows_trans (grows_trans g0 grows1) grows2
      dsimp only [ReadOk]
      refine ⟨⟨subjectView t.subject, owlPropertyChainAxiom, objectView t.object⟩ ::
          ((listOf cells nodes).2 ++ q ++ ps), f1 ++ (cells ++ f2), grows_same whole ?_, fun rest => ?_⟩
      · intro x
        simp only [List.mem_cons, List.mem_append]
        tauto
      · have statement := TAxiom.propertyChain chain sup cells (f1 ++ (cells ++ (f2 ++ rest))) (f2 ++ rest) rest
          (objectView node) nodes q ps (tope _) lengths (topes rest)
        rw [head, view] at statement
        simpa only [List.append_assoc] using statement

theorem equivalent_property_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (predicate : t.predicate.spelling.val = owlEquivalentProperty) (r : rdf_mapping.Read)
    (ran : rdf_mapping.equivalent_property triples kinds index s = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.equivalent_property] at ran
  simp only [take_correct, bind_ok] at ran
  have g0 := take_main triples s index t unused
  rw [predicate] at g0
  obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some pk =>
    cases pk with
    | Annotation => simp at ran; subst ran; trivial
    | Object =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨p1, p2, s2⟩ := p
        simp [rdf_mapping.two] at ran
        subst ran
        obtain ⟨q1, q2, f1, f2, grows, tope1, tope2⟩ := property_pair_spec triples index _ s2 t unused.1 p1 p2 pairRun
        dsimp only [ReadOk]
        refine ⟨⟨subjectView t.subject, owlEquivalentProperty, objectView t.object⟩ :: (q1 ++ q2), f1 ++ f2,
          by simpa using grows_trans g0 grows, fun rest => ?_⟩
        have topes : TOPEs [p1, p2] (f1 ++ (f2 ++ rest)) [subjectView t.subject, objectView t.object]
            (q1 ++ (q2 ++ [])) rest :=
          .cons p1 [p2] _ _ _ _ _ q1 (q2 ++ []) (tope1 _) (.cons p2 [] _ _ _ _ _ q2 [] (tope2 rest) (.nil rest))
        simpa [chainOf] using TAxiom.equivalentObjectProperties ⟨p1, p2, alloc.vec.Vec.new _⟩ _ _ _ _ topes
    | Data =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨d1, d2⟩ := p
        simp [rdf_mapping.two] at ran
        subst ran
        obtain ⟨v1, v2⟩ := data_pair_spec triples index t unused.1 d1 d2 pairRun
        rw [← v1, ← v2] at g0
        dsimp only [ReadOk]
        refine ⟨_, [], g0, fun rest => ?_⟩
        have statement : TAxiom (.EquivalentDataProperties ⟨d1, d2, alloc.vec.Vec.new _⟩) rest
            [⟨iriNode d1.iri, owlEquivalentProperty, iriNode d2.iri⟩] rest :=
          TAxiom.equivalentDataProperties ⟨d1, d2, alloc.vec.Vec.new _⟩ rest
        exact statement

theorem disjoint_property_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (predicate : t.predicate.spelling.val = owlPropertyDisjointWith) (r : rdf_mapping.Read)
    (ran : rdf_mapping.disjoint_property triples kinds index s = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.disjoint_property] at ran
  simp only [take_correct, bind_ok] at ran
  have g0 := take_main triples s index t unused
  rw [predicate] at g0
  obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some pk =>
    cases pk with
    | Annotation => simp at ran; subst ran; trivial
    | Object =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨p1, p2, s2⟩ := p
        simp [rdf_mapping.two] at ran
        subst ran
        obtain ⟨q1, q2, f1, f2, grows, tope1, tope2⟩ := property_pair_spec triples index _ s2 t unused.1 p1 p2 pairRun
        dsimp only [ReadOk]
        refine ⟨⟨subjectView t.subject, owlPropertyDisjointWith, objectView t.object⟩ :: (q1 ++ q2), f1 ++ f2,
          by simpa using grows_trans g0 grows, fun rest => ?_⟩
        simpa using TAxiom.disjointObjectProperties p1 p2 (f1 ++ (f2 ++ rest)) (f2 ++ rest) rest _ _ q1 q2
          (tope1 _) (tope2 rest)
    | Data =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨d1, d2⟩ := p
        simp [rdf_mapping.two] at ran
        subst ran
        obtain ⟨v1, v2⟩ := data_pair_spec triples index t unused.1 d1 d2 pairRun
        rw [← v1, ← v2] at g0
        dsimp only [ReadOk]
        exact ⟨_, [], g0, fun rest => TAxiom.disjointDataProperties d1 d2 rest⟩

theorem inverse_properties_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (s : rdf_mapping.State)
    (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (predicate : t.predicate.spelling.val = owlInverseOf) (r : rdf_mapping.Read)
    (ran : rdf_mapping.inverse_properties triples index s = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.inverse_properties] at ran
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, bind_ok] at ran
  cases subject : t.subject with
  | Blank _ => simp [subject] at ran; subst ran; exact grows_refl _ _
  | Iri _ =>
    simp only [subject, take_correct, bind_ok] at ran
    obtain ⟨o, pairRun, ran⟩ := bind_eq_ok ran
    cases o with
    | none => simp at ran; subst ran; trivial
    | some p =>
      obtain ⟨p1, p2, s2⟩ := p
      simp at ran
      subst ran
      obtain ⟨q1, q2, f1, f2, grows, tope1, tope2⟩ := property_pair_spec triples index _ s2 t unused.1 p1 p2 pairRun
      have g0 := take_main triples s index t unused
      rw [predicate] at g0
      dsimp only [ReadOk]
      refine ⟨⟨subjectView t.subject, owlInverseOf, objectView t.object⟩ :: (q1 ++ q2), f1 ++ f2,
        by simpa using grows_trans g0 grows, fun rest => ?_⟩
      simpa using TAxiom.inverseProperties p1 p2 (f1 ++ (f2 ++ rest)) (f2 ++ rest) rest _ _ q1 q2 (tope1 _)
        (tope2 rest)

theorem domain_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (predicate : t.predicate.spelling.val = rdfsDomain)
    (r : rdf_mapping.Read) (ran : rdf_mapping.domain_range triples kinds index s false fuel = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.domain_range] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, nodeRun,
    bind_ok, Bool.false_eq_true, ↓reduceIte] at ran
  have g0 := take_main triples s index t unused
  rw [predicate] at g0
  obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some pk =>
    cases pk with
    | Object =>
      simp only at ran
      obtain ⟨o1, roleRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨role, s2⟩ := p
        obtain ⟨o2, classRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran; subst ran; trivial
        | some p1 =>
          obtain ⟨filler, s3⟩ := p1
          simp at ran
          subst ran
          obtain ⟨q1, f1, grows1, tope⟩ := property_expression_spec triples node _ s2 role roleRun
          obtain ⟨q2, f2, grows2, tce⟩ := class_expression_right triples kinds fuel t.object s2 s3 filler classRun
          dsimp only [ReadOk]
          refine ⟨⟨subjectView t.subject, rdfsDomain, objectView t.object⟩ :: (q1 ++ q2), f1 ++ f2,
            by simpa using grows_trans (grows_trans g0 grows1) grows2, fun rest => ?_⟩
          have statement := TAxiom.objectDomain role filler (f1 ++ (f2 ++ rest)) (f2 ++ rest) rest _ _ q1 q2
            (tope _) (tce rest)
          rw [view] at statement
          simpa using statement
    | Data =>
      simp only at ran
      obtain ⟨o1, iriRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some iri =>
        have subjectIs : subjectView t.subject = iriNode iri := by
          rw [← view]
          exact node_iri_spec node iri iriRun
        simp only at ran
        obtain ⟨o2, classRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran; subst ran; trivial
        | some p =>
          obtain ⟨filler, s2⟩ := p
          simp at ran
          subst ran
          obtain ⟨q, f, grows, tce⟩ := class_expression_right triples kinds fuel t.object _ s2 filler classRun
          rw [subjectIs] at g0
          dsimp only [ReadOk]
          exact ⟨⟨iriNode iri, rdfsDomain, objectView t.object⟩ :: q, f, by simpa using grows_trans g0 grows,
            fun rest => TAxiom.dataDomain ⟨iri⟩ filler (f ++ rest) rest _ q (tce rest)⟩
    | Annotation =>
      simp only at ran
      obtain ⟨o1, iriRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some iri =>
        simp only at ran
        obtain ⟨o2, targetRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran; subst ran; trivial
        | some target =>
          simp at ran
          subst ran
          have subjectIs : subjectView t.subject = iriNode iri := by
            rw [← view]
            exact node_iri_spec node iri iriRun
          rw [subjectIs, node_iri_spec t.object target targetRun] at g0
          dsimp only [ReadOk]
          exact ⟨_, [], g0, fun rest => TAxiom.annotationDomain ⟨iri⟩ target rest⟩

theorem range_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (predicate : t.predicate.spelling.val = rdfsRange)
    (r : rdf_mapping.Read) (ran : rdf_mapping.domain_range triples kinds index s true fuel = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.domain_range] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, nodeRun,
    bind_ok, eq_self_iff_true, if_true] at ran
  have g0 := take_main triples s index t unused
  rw [predicate] at g0
  obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some pk =>
    cases pk with
    | Object =>
      simp only at ran
      obtain ⟨o1, roleRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨role, s2⟩ := p
        obtain ⟨o2, classRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran; subst ran; trivial
        | some p1 =>
          obtain ⟨filler, s3⟩ := p1
          simp at ran
          subst ran
          obtain ⟨q1, f1, grows1, tope⟩ := property_expression_spec triples node _ s2 role roleRun
          obtain ⟨q2, f2, grows2, tce⟩ := class_expression_right triples kinds fuel t.object s2 s3 filler classRun
          dsimp only [ReadOk]
          refine ⟨⟨subjectView t.subject, rdfsRange, objectView t.object⟩ :: (q1 ++ q2), f1 ++ f2,
            by simpa using grows_trans (grows_trans g0 grows1) grows2, fun rest => ?_⟩
          have statement := TAxiom.objectRange role filler (f1 ++ (f2 ++ rest)) (f2 ++ rest) rest _ _ q1 q2
            (tope _) (tce rest)
          rw [view] at statement
          simpa using statement
    | Data =>
      simp only at ran
      obtain ⟨o1, iriRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some iri =>
        have subjectIs : subjectView t.subject = iriNode iri := by
          rw [← view]
          exact node_iri_spec node iri iriRun
        simp only at ran
        obtain ⟨o2, rangeRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran; subst ran; trivial
        | some p =>
          obtain ⟨filler, s2⟩ := p
          simp at ran
          subst ran
          obtain ⟨q, f, grows, tdr⟩ := data_range_right triples kinds fuel t.object _ s2 filler rangeRun
          rw [subjectIs] at g0
          dsimp only [ReadOk]
          exact ⟨⟨iriNode iri, rdfsRange, objectView t.object⟩ :: q, f, by simpa using grows_trans g0 grows,
            fun rest => TAxiom.dataRange ⟨iri⟩ filler (f ++ rest) rest _ q (tdr rest)⟩
    | Annotation =>
      simp only at ran
      obtain ⟨o1, iriRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some iri =>
        simp only at ran
        obtain ⟨o2, targetRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran; subst ran; trivial
        | some target =>
          simp at ran
          subst ran
          have subjectIs : subjectView t.subject = iriNode iri := by
            rw [← view]
            exact node_iri_spec node iri iriRun
          rw [subjectIs, node_iri_spec t.object target targetRun] at g0
          dsimp only [ReadOk]
          exact ⟨_, [], g0, fun rest => TAxiom.annotationRange ⟨iri⟩ target rest⟩

theorem same_individual_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (s : rdf_mapping.State)
    (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (predicate : t.predicate.spelling.val = owlSameAs) (r : rdf_mapping.Read)
    (ran : rdf_mapping.same_individual triples index s = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.same_individual] at ran
  obtain ⟨o, pairRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨a, b⟩ := p
    simp [rdf_mapping.two, take_correct] at ran
    subst ran
    obtain ⟨va, vb⟩ := individual_pair_spec triples index t unused.1 a b pairRun
    have g0 := take_main triples s index t unused
    rw [predicate, ← va, ← vb] at g0
    dsimp only [ReadOk]
    refine ⟨_, [], g0, fun rest => ?_⟩
    have statement : TAxiom (.SameIndividual ⟨a, b, alloc.vec.Vec.new _⟩) rest
        [⟨individualNode a, owlSameAs, individualNode b⟩] rest :=
      TAxiom.sameIndividual ⟨a, b, alloc.vec.Vec.new _⟩ rest
    exact statement

theorem different_individuals_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (s : rdf_mapping.State)
    (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (predicate : t.predicate.spelling.val = owlDifferentFrom) (r : rdf_mapping.Read)
    (ran : rdf_mapping.different_individuals triples index s = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.different_individuals] at ran
  obtain ⟨o, pairRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨a, b⟩ := p
    simp [rdf_mapping.two, take_correct] at ran
    subst ran
    obtain ⟨va, vb⟩ := individual_pair_spec triples index t unused.1 a b pairRun
    have g0 := take_main triples s index t unused
    rw [predicate, ← va, ← vb] at g0
    dsimp only [ReadOk]
    exact ⟨_, [], g0, fun rest => TAxiom.differentIndividuals a b rest⟩

theorem has_key_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (predicate : t.predicate.spelling.val = owlHasKey)
    (r : rdf_mapping.Read) (ran : rdf_mapping.has_key triples kinds index s fuel = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.has_key] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, nodeRun,
    bind_ok] at ran
  obtain ⟨o, classRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨c, s2⟩ := p
    obtain ⟨o1, cellsRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran; subst ran; trivial
    | some p1 =>
      obtain ⟨firsts, s3⟩ := p1
      obtain ⟨o2, keysRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran; subst ran; trivial
      | some p2 =>
        obtain ⟨objects, datas, s4⟩ := p2
        simp at ran
        subst ran
        obtain ⟨pc, fc, grows1, tce⟩ := class_expression_right triples kinds fuel node _ s2 c classRun
        obtain ⟨news, cells, split, lengths, grows2, head⟩ := cells_spec triples fuel.val fuel t.object s2 s3 _ firsts
          rfl cellsRun
        simp at split
        obtain ⟨newObjs, newDatas, nodes, pk, fk, splitO, splitD, -, grows3, joined, topes⟩ := key_members_spec
          triples kinds firsts 0#usize s3 s4 _ objects _ datas keysRun
        simp at splitO splitD
        simp only [show (0#usize).val = 0 from rfl] at joined
        have start : news.map (elementNode triples.val) = elementsFrom triples.val firsts.val 0 := by
          simp [elementsFrom, split]
        have whole : nodes ++ datas.val.map (iriNode ·.iri) = news.map (elementNode triples.val) := by
          rw [start, splitD, joined]
        have g0 := take_main triples s index t unused
        rw [predicate] at g0
        have chain : Grows triples.val s s4
            (⟨subjectView t.subject, owlHasKey, objectView t.object⟩ ::
              (pc ++ ((listOf cells (news.map (elementNode triples.val))).2 ++ pk))) (fc ++ (cells ++ fk)) := by
          simpa using grows_trans (grows_trans (grows_trans g0 grows1) grows2) grows3
        dsimp only [ReadOk]
        refine ⟨⟨subjectView t.subject, owlHasKey, objectView t.object⟩ ::
            ((listOf cells (news.map (elementNode triples.val))).2 ++ pc ++ pk), fc ++ (cells ++ fk),
          grows_same chain ?_, fun rest => ?_⟩
        · intro x
          simp only [List.mem_cons, List.mem_append]
          tauto
        · have count : cells.length = objects.val.length + datas.val.length := by
            have n1 := topes_length (topes [])
            have n2 := congrArg List.length joined
            simp [elementsFrom] at n2
            rw [splitO, splitD, n1, lengths, ← split]
            omega
          have statement := TAxiom.hasKey c objects datas cells (fc ++ (cells ++ (fk ++ rest))) (fk ++ rest) rest _
            nodes pc pk (tce _) count (by rw [splitO]; exact topes rest)
          rw [whole, head, view] at statement
          simpa only [List.append_assoc] using statement

/-- The type IRI of each characteristic code. -/
def characteristicWord (kind : U8) : List U8 :=
  if kind = 0#u8 then owlFunctionalProperty
  else if kind = 1#u8 then owlInverseFunctionalProperty
  else if kind = 2#u8 then owlReflexiveProperty
  else if kind = 3#u8 then owlIrreflexiveProperty
  else if kind = 4#u8 then owlSymmetricProperty
  else if kind = 5#u8 then owlAsymmetricProperty
  else owlTransitiveProperty

theorem characteristic_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (typed : t.predicate.spelling.val = rdfType) (kind : U8)
    (object : objectView t.object = .iri (characteristicWord kind)) (r : rdf_mapping.Read)
    (ran : rdf_mapping.characteristic triples kinds index s kind = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.characteristic] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, nodeRun,
    bind_ok] at ran
  have g0 := take_main triples s index t unused
  rw [typed, object] at g0
  obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some pk =>
    cases pk with
    | Annotation => simp at ran; subst ran; trivial
    | Object =>
      simp only at ran
      obtain ⟨o1, roleRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨role, s2⟩ := p
        obtain ⟨q, f, grows, tope⟩ := property_expression_spec triples node _ s2 role roleRun
        have found : ∃ a, r = .Found a s2 ∧ characteristicType a = some (role, characteristicWord kind) := by
          by_cases k0 : kind = 0#u8
          · simp [if_pos k0] at ran
            subst ran
            exact ⟨_, rfl, by simp only [characteristicType, characteristicWord, if_pos k0]⟩
          by_cases k1 : kind = 1#u8
          · simp [if_neg k0, if_pos k1] at ran
            subst ran
            exact ⟨_, rfl, by simp only [characteristicType, characteristicWord, if_neg k0, if_pos k1]⟩
          by_cases k2 : kind = 2#u8
          · simp [if_neg k0, if_neg k1, if_pos k2] at ran
            subst ran
            exact ⟨_, rfl, by simp only [characteristicType, characteristicWord, if_neg k0, if_neg k1, if_pos k2]⟩
          by_cases k3 : kind = 3#u8
          · simp [if_neg k0, if_neg k1, if_neg k2, if_pos k3] at ran
            subst ran
            exact ⟨_, rfl, by
              simp only [characteristicType, characteristicWord, if_neg k0, if_neg k1, if_neg k2, if_pos k3]⟩
          by_cases k4 : kind = 4#u8
          · simp [if_neg k0, if_neg k1, if_neg k2, if_neg k3, if_pos k4] at ran
            subst ran
            exact ⟨_, rfl, by simp only [characteristicType, characteristicWord, if_neg k0, if_neg k1, if_neg k2,
              if_neg k3, if_pos k4]⟩
          by_cases k5 : kind = 5#u8
          · simp [if_neg k0, if_neg k1, if_neg k2, if_neg k3, if_neg k4, if_pos k5] at ran
            subst ran
            exact ⟨_, rfl, by simp only [characteristicType, characteristicWord, if_neg k0, if_neg k1, if_neg k2,
              if_neg k3, if_neg k4, if_pos k5]⟩
          · simp [if_neg k0, if_neg k1, if_neg k2, if_neg k3, if_neg k4, if_neg k5] at ran
            subst ran
            exact ⟨_, rfl, by simp only [characteristicType, characteristicWord, if_neg k0, if_neg k1, if_neg k2,
              if_neg k3, if_neg k4, if_neg k5]⟩
        obtain ⟨a, rfl, kindIs⟩ := found
        dsimp only [ReadOk]
        refine ⟨⟨subjectView t.subject, rdfType, .iri (characteristicWord kind)⟩ :: q, f,
          by simpa using grows_trans g0 grows, fun rest => ?_⟩
        have role' := tope rest
        rw [view] at role'
        exact TAxiom.characteristic a role _ (f ++ rest) rest _ q kindIs role'
    | Data =>
      simp only at ran
      by_cases k0 : kind = 0#u8
      · simp only [if_pos k0] at ran
        obtain ⟨o1, iriRun, ran⟩ := bind_eq_ok ran
        cases o1 with
        | none => simp at ran; subst ran; trivial
        | some iri =>
          simp at ran
          subst ran
          have word : characteristicWord kind = owlFunctionalProperty := by
            simp only [characteristicWord, if_pos k0]
          have subjectIs : subjectView t.subject = iriNode iri := by
            rw [← view]
            exact node_iri_spec node iri iriRun
          rw [word, subjectIs] at g0
          dsimp only [ReadOk]
          exact ⟨_, [], g0, fun rest => TAxiom.functionalData ⟨iri⟩ rest⟩
      · simp only [if_neg k0] at ran
        simp at ran
        subst ran
        trivial

theorem axiom_node_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (s s' : rdf_mapping.State)
    (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t) (blank : rdf.BlankNode)
    (ran : rdf_mapping.axiom_node triples index s = .ok (some (blank, s'))) :
    Grows triples.val s s' [⟨.blank blank, t.predicate.spelling.val, objectView t.object⟩] [blank] := by
  rw [rdf_mapping.axiom_node] at ran
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, bind_ok] at ran
  have g0 := take_main triples s index t unused
  cases subject : t.subject with
  | Iri _ => simp [subject] at ran
  | Blank b =>
    simp only [subject, take_correct, bind_ok] at ran
    obtain ⟨s2, recordRun, ran⟩ := bind_eq_ok ran
    simp only [copy_blank_identity, bind_ok, Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    rw [subject] at g0
    simpa [subjectView] using grows_trans g0 (grows_record triples.val _ s2 b recordRun)

theorem all_disjoint_classes_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (typed : t.predicate.spelling.val = rdfType)
    (object : objectView t.object = .iri owlAllDisjointClasses) (r : rdf_mapping.Read)
    (ran : rdf_mapping.all_disjoint_classes triples kinds index s fuel = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.all_disjoint_classes] at ran
  obtain ⟨o, nodeRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨blank, s1⟩ := p
    have g0 := axiom_node_spec triples index s s1 t unused blank nodeRun
    rw [typed, object] at g0
    simp only [lift, bind_ok] at ran
    obtain ⟨o1, findRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran; subst ran; trivial
    | some list =>
      obtain ⟨t1, lookup1, g1⟩ := found_take triples s1 blank _ owlMembers (by simp [slice_val, owlMembers]) list
        findRun
      simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup1, bind_ok] at ran
      obtain ⟨o2, listRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran; subst ran; trivial
      | some p1 =>
        obtain ⟨members, s3⟩ := p1
        by_cases more : 1 ≤ members.rest.val.length
        · simp [more] at ran
          subst ran
          obtain ⟨cells, nodes, patterns, fresh, lengths, grows, head, tces⟩ := class_list2_spec triples kinds fuel
            (class_expression_right triples kinds fuel) t1.object _ s3 members listRun
          dsimp only [ReadOk]
          refine ⟨⟨.blank blank, rdfType, .iri owlAllDisjointClasses⟩ :: ⟨.blank blank, owlMembers, objectView t1.object⟩ ::
              ((listOf cells nodes).2 ++ patterns), blank :: (cells ++ fresh),
            by simpa using grows_trans (grows_trans g0 g1) grows, fun rest => ?_⟩
          have nonempty : members.rest.val ≠ [] := by
            intro h
            rw [h] at more
            simp at more
          have statement := TAxiom.allDisjointClasses members blank cells (fresh ++ rest) rest nodes patterns nonempty
            lengths (tces rest)
          rw [head] at statement
          simpa only [List.append_assoc, List.cons_append] using statement
        · simp [more] at ran
          subst ran
          trivial

theorem all_disjoint_properties_spec (triples : alloc.vec.Vec rdf.Triple)
    (kinds : alloc.vec.Vec rdf_mapping.Declared) (index : Usize) (s : rdf_mapping.State) (fuel : Usize)
    (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (typed : t.predicate.spelling.val = rdfType) (object : objectView t.object = .iri owlAllDisjointProperties)
    (r : rdf_mapping.Read) (ran : rdf_mapping.all_disjoint_properties triples kinds index s fuel = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.all_disjoint_properties] at ran
  obtain ⟨o, nodeRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨blank, s1⟩ := p
    have g0 := axiom_node_spec triples index s s1 t unused blank nodeRun
    rw [typed, object] at g0
    simp only [lift, bind_ok] at ran
    obtain ⟨o1, findRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran; subst ran; trivial
    | some list =>
      obtain ⟨t1, lookup1, g1⟩ := found_take triples s1 blank _ owlMembers (by simp [slice_val, owlMembers]) list
        findRun
      simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup1, bind_ok] at ran
      obtain ⟨o2, kindRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran; subst ran; trivial
      | some pk =>
        cases pk with
        | Annotation => simp at ran; subst ran; trivial
        | Object =>
          simp only at ran
          obtain ⟨o3, listRun, ran⟩ := bind_eq_ok ran
          cases o3 with
          | none => simp at ran; subst ran; trivial
          | some p1 =>
            obtain ⟨members, s3⟩ := p1
            by_cases more : 1 ≤ members.rest.val.length
            · simp [more] at ran
              subst ran
              obtain ⟨cells, nodes, patterns, fresh, lengths, grows, head, topes⟩ := property_list2_spec triples kinds
                t1.object _ s3 fuel members listRun
              dsimp only [ReadOk]
              refine ⟨⟨.blank blank, rdfType, .iri owlAllDisjointProperties⟩ ::
                  ⟨.blank blank, owlMembers, objectView t1.object⟩ :: ((listOf cells nodes).2 ++ patterns),
                blank :: (cells ++ fresh), by simpa using grows_trans (grows_trans g0 g1) grows, fun rest => ?_⟩
              have nonempty : members.rest.val ≠ [] := by
                intro h
                rw [h] at more
                simp at more
              have statement := TAxiom.allDisjointObjectProperties members blank cells (fresh ++ rest) rest nodes
                patterns nonempty lengths (topes rest)
              rw [head] at statement
              simpa only [List.append_assoc, List.cons_append] using statement
            · simp [more] at ran
              subst ran
              trivial
        | Data =>
          simp only at ran
          obtain ⟨o3, listRun, ran⟩ := bind_eq_ok ran
          cases o3 with
          | none => simp at ran; subst ran; trivial
          | some p1 =>
            obtain ⟨members, s3⟩ := p1
            by_cases more : 1 ≤ members.rest.val.length
            · simp [more] at ran
              subst ran
              obtain ⟨cells, lengths, grows, head⟩ := data_list2_spec triples kinds t1.object _ s3 fuel members listRun
              dsimp only [ReadOk]
              refine ⟨⟨.blank blank, rdfType, .iri owlAllDisjointProperties⟩ ::
                  ⟨.blank blank, owlMembers, objectView t1.object⟩ ::
                  (listOf cells ((members2 members).map (iriNode ·.iri))).2,
                blank :: cells, by simpa using grows_trans (grows_trans g0 g1) grows, fun rest => ?_⟩
              have nonempty : members.rest.val ≠ [] := by
                intro h
                rw [h] at more
                simp at more
              have statement := TAxiom.allDisjointDataProperties members blank cells rest nonempty lengths
              rw [head] at statement
              simpa only [List.append_assoc, List.cons_append] using statement
            · simp [more] at ran
              subst ran
              trivial

theorem all_different_spec (triples : alloc.vec.Vec rdf.Triple) (index : Usize) (s : rdf_mapping.State)
    (fuel : Usize) (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (typed : t.predicate.spelling.val = rdfType) (object : objectView t.object = .iri owlAllDifferent)
    (r : rdf_mapping.Read) (ran : rdf_mapping.all_different triples index s fuel = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.all_different] at ran
  obtain ⟨o, nodeRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨blank, s1⟩ := p
    have g0 := axiom_node_spec triples index s s1 t unused blank nodeRun
    rw [typed, object] at g0
    simp only [lift, bind_ok] at ran
    obtain ⟨o1, findRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran; subst ran; trivial
    | some list =>
      obtain ⟨t1, lookup1, g1⟩ := found_take triples s1 blank _ owlMembers (by simp [slice_val, owlMembers]) list
        findRun
      simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup1, bind_ok] at ran
      obtain ⟨o2, listRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran; subst ran; trivial
      | some p1 =>
        obtain ⟨members, s3⟩ := p1
        by_cases more : 1 ≤ members.rest.val.length
        · simp [more] at ran
          subst ran
          obtain ⟨cells, lengths, grows, head⟩ := individual_list2_spec triples t1.object _ s3 fuel members listRun
          dsimp only [ReadOk]
          refine ⟨⟨.blank blank, rdfType, .iri owlAllDifferent⟩ :: ⟨.blank blank, owlMembers, objectView t1.object⟩ ::
              (listOf cells ((members2 members).map individualNode)).2,
            blank :: cells, by simpa using grows_trans (grows_trans g0 g1) grows, fun rest => ?_⟩
          have nonempty : members.rest.val ≠ [] := by
            intro h
            rw [h] at more
            simp at more
          have statement := TAxiom.allDifferent members blank cells rest nonempty lengths
          rw [head] at statement
          simpa only [List.append_assoc, List.cons_append] using statement
        · simp [more] at ran
          subst ran
          trivial

theorem negative_assertion_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (typed : t.predicate.spelling.val = rdfType) (object : objectView t.object = .iri owlNegativePropertyAssertion)
    (r : rdf_mapping.Read) (ran : rdf_mapping.negative_assertion triples kinds index s = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.negative_assertion] at ran
  obtain ⟨o, nodeRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some p =>
    obtain ⟨blank, s1⟩ := p
    have g0 := axiom_node_spec triples index s s1 t unused blank nodeRun
    rw [typed, object] at g0
    simp only [lift, bind_ok] at ran
    obtain ⟨o1, sourceRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran; subst ran; trivial
    | some source =>
      obtain ⟨t1, lookup1, g1⟩ := found_take triples s1 blank _ owlSourceIndividual
        (by simp [slice_val, owlSourceIndividual]) source sourceRun
      simp only [alloc.vec.Vec.index_slice_index, lookup1, bind_ok] at ran
      obtain ⟨o2, subjectRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran; subst ran; trivial
      | some a =>
        simp only [take_correct, bind_ok] at ran
        obtain ⟨o3, propertyRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran; subst ran; trivial
        | some property =>
          obtain ⟨t2, lookup2, g2⟩ := found_take triples { s1 with used := s1.used.set source true } blank _
            owlAssertionProperty (by simp [slice_val, owlAssertionProperty]) property propertyRun
          simp only [take_correct, alloc.vec.Vec.index_slice_index, lookup2, bind_ok] at ran
          rw [node_individual_spec _ a subjectRun] at g1
          obtain ⟨o4, kindRun, ran⟩ := bind_eq_ok ran
          cases o4 with
          | none => simp at ran; subst ran; trivial
          | some pk =>
            cases pk with
            | Annotation => simp at ran; subst ran; trivial
            | Object =>
              simp only at ran
              obtain ⟨o5, roleRun, ran⟩ := bind_eq_ok ran
              cases o5 with
              | none => simp at ran; subst ran; trivial
              | some p1 =>
                obtain ⟨role, s4⟩ := p1
                obtain ⟨q, f, g3, tope⟩ := property_expression_spec triples t2.object _ s4 role roleRun
                obtain ⟨o6, targetRun, ran⟩ := bind_eq_ok ran
                cases o6 with
                | none => simp at ran; subst ran; trivial
                | some target =>
                  obtain ⟨t3, lookup3, g4⟩ := found_take triples s4 blank _ owlTargetIndividual
                    (by simp [slice_val, owlTargetIndividual]) target targetRun
                  simp only [alloc.vec.Vec.index_slice_index, lookup3, bind_ok] at ran
                  obtain ⟨o7, objectRun, ran⟩ := bind_eq_ok ran
                  cases o7 with
                  | none => simp at ran; subst ran; trivial
                  | some b =>
                    simp [take_correct] at ran
                    subst ran
                    rw [node_individual_spec _ b objectRun] at g4
                    have chain : Grows triples.val s { s4 with used := s4.used.set target true }
                        (⟨.blank blank, rdfType, .iri owlNegativePropertyAssertion⟩ ::
                          ⟨.blank blank, owlSourceIndividual, individualNode a⟩ ::
                          ⟨.blank blank, owlAssertionProperty, objectView t2.object⟩ ::
                          (q ++ [⟨.blank blank, owlTargetIndividual, individualNode b⟩])) (blank :: f) := by
                      simpa using grows_trans (grows_trans (grows_trans (grows_trans g0 g1) g2) g3) g4
                    dsimp only [ReadOk]
                    refine ⟨⟨.blank blank, rdfType, .iri owlNegativePropertyAssertion⟩ ::
                        ⟨.blank blank, owlSourceIndividual, individualNode a⟩ ::
                        ⟨.blank blank, owlAssertionProperty, objectView t2.object⟩ ::
                        ⟨.blank blank, owlTargetIndividual, individualNode b⟩ :: q, blank :: f,
                      grows_same chain ?_, fun rest => TAxiom.negativeObject role a b blank (f ++ rest) rest _ q (tope rest)⟩
                    intro x
                    simp only [List.mem_cons, List.mem_append, List.mem_singleton]
                    tauto
            | Data =>
              simp only at ran
              obtain ⟨o5, iriRun, ran⟩ := bind_eq_ok ran
              cases o5 with
              | none => simp at ran; subst ran; trivial
              | some iri =>
                simp only at ran
                obtain ⟨o6, targetRun, ran⟩ := bind_eq_ok ran
                cases o6 with
                | none => simp at ran; subst ran; trivial
                | some target =>
                  obtain ⟨t3, lookup3, g4⟩ := found_take triples
                    { s1 with used := (s1.used.set source true).set property true } blank _ owlTargetValue
                    (by simp [slice_val, owlTargetValue]) target targetRun
                  simp only [alloc.vec.Vec.index_slice_index, lookup3, bind_ok] at ran
                  obtain ⟨o7, valueRun, ran⟩ := bind_eq_ok ran
                  cases o7 with
                  | none => simp at ran; subst ran; trivial
                  | some value =>
                    simp [take_correct] at ran
                    subst ran
                    rw [node_iri_spec _ iri iriRun] at g2
                    dsimp only [ReadOk]
                    exact ⟨_, [blank], by simpa using grows_trans (grows_trans (grows_trans g0 g1) g2) g4,
                      fun rest => TAxiom.negativeData ⟨iri⟩ a value blank rest _ (node_literal_spec _ value valueRun)⟩

theorem class_assertion_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (typed : t.predicate.spelling.val = rdfType)
    (r : rdf_mapping.Read) (ran : rdf_mapping.class_assertion triples kinds index s fuel = .ok r) :
    ReadOk triples s r := by
  rw [rdf_mapping.class_assertion] at ran
  obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
  simp only [take_correct, alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, nodeRun,
    bind_ok] at ran
  obtain ⟨o, individualRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some a =>
    simp only at ran
    obtain ⟨o1, classRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none => simp at ran; subst ran; trivial
    | some p =>
      obtain ⟨c, s2⟩ := p
      simp at ran
      subst ran
      obtain ⟨q, f, grows, tce⟩ := class_expression_right triples kinds fuel t.object _ s2 c classRun
      have g0 := take_main triples s index t unused
      have subjectIs : subjectView t.subject = individualNode a := by
        rw [← view]
        exact node_individual_spec node a individualRun
      rw [typed, subjectIs] at g0
      dsimp only [ReadOk]
      exact ⟨⟨individualNode a, rdfType, objectView t.object⟩ :: q, f, by simpa using grows_trans g0 grows,
        fun rest => TAxiom.classAssertion c a (f ++ rest) rest _ q (tce rest)⟩

theorem assertion_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (t : rdf.Triple) (unused : Unused triples.val s.used.val index.val t)
    (r : rdf_mapping.Read) (ran : rdf_mapping.assertion triples kinds index s = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.assertion] at ran
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, bind_ok] at ran
  have g0 := take_main triples s index t unused
  obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran; subst ran; trivial
  | some pk =>
    cases pk with
    | Object =>
      simp only at ran
      obtain ⟨o1, pairRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some p =>
        obtain ⟨a, b⟩ := p
        simp [iri_of_identity, take_correct] at ran
        subst ran
        obtain ⟨va, vb⟩ := individual_pair_spec triples index t unused.1 a b pairRun
        rw [← va, ← vb] at g0
        dsimp only [ReadOk]
        exact ⟨_, [], g0, fun rest => TAxiom.objectAssertion ⟨⟨t.predicate.spelling⟩⟩ a b rest⟩
    | Data =>
      obtain ⟨node, nodeRun, view⟩ := subject_node_view t.subject
      simp only [nodeRun, bind_ok] at ran
      obtain ⟨o1, individualRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some a =>
        simp only at ran
        obtain ⟨o2, literalRun, ran⟩ := bind_eq_ok ran
        cases o2 with
        | none => simp at ran; subst ran; trivial
        | some value =>
          simp [iri_of_identity, take_correct] at ran
          subst ran
          have subjectIs : subjectView t.subject = individualNode a := by
            rw [← view]
            exact node_individual_spec node a individualRun
          rw [subjectIs] at g0
          dsimp only [ReadOk]
          exact ⟨_, [], g0, fun rest => TAxiom.dataAssertion ⟨⟨t.predicate.spelling⟩⟩ a value rest _
            (node_literal_spec _ value literalRun)⟩
    | Annotation =>
      simp only at ran
      obtain ⟨o1, valueRun, ran⟩ := bind_eq_ok ran
      cases o1 with
      | none => simp at ran; subst ran; trivial
      | some value =>
        simp only [iri_of_identity, bind_ok] at ran
        obtain ⟨subject, subjectRun, ran⟩ := bind_eq_ok ran
        simp [take_correct] at ran
        subst ran
        rw [← annotation_subject_spec t.subject subject subjectRun] at g0
        dsimp only [ReadOk]
        exact ⟨_, [], g0, fun rest => TAxiom.annotationAssertion ⟨⟨t.predicate.spelling⟩⟩ subject value rest _
          (annotation_value_spec _ value valueRun)⟩

/-! ### Reading the axioms of a graph -/

theorem typing_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (typed : t.predicate.spelling.val = rdfType)
    (r : rdf_mapping.Read) (ran : rdf_mapping.typing triples kinds index s fuel = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.typing] at ran
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, lift, bind_ok,
    object_is_correct] at ran
  repeat rw [slice_val] at ran
  by_cases h0 : objectView t.object = .iri owlRestriction
  · simp only [owlRestriction] at h0
    simp only [h0, decide_true, ↓reduceIte] at ran
    obtain ⟨b, -, ran⟩ := bind_eq_ok ran
    cases b
    · simp at ran; subst ran; trivial
    · simp at ran; subst ran; exact grows_refl _ _
  simp only [owlRestriction] at h0
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h1 : objectView t.object = .iri owlClass
  · simp only [owlClass] at h1
    simp only [h1, decide_true, ↓reduceIte] at ran
    obtain ⟨b, -, ran⟩ := bind_eq_ok ran
    cases b
    · simp at ran; subst ran; trivial
    · simp at ran; subst ran; exact grows_refl _ _
  simp only [owlClass] at h1
  simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h2 : objectView t.object = .iri rdfsDatatype
  · simp only [rdfsDatatype] at h2
    simp only [h2, decide_true, ↓reduceIte] at ran
    obtain ⟨b, -, ran⟩ := bind_eq_ok ran
    cases b
    · simp at ran; subst ran; trivial
    · simp at ran; subst ran; exact grows_refl _ _
  simp only [rdfsDatatype] at h2
  simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h3 : objectView t.object = .iri owlFunctionalProperty
  · have word : objectView t.object = .iri (characteristicWord 0#u8) := h3
    simp only [owlFunctionalProperty] at h3
    simp only [h3, decide_true, ↓reduceIte] at ran
    exact characteristic_spec triples kinds index s t unused typed 0#u8 word r ran
  simp only [owlFunctionalProperty] at h3
  simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h4 : objectView t.object = .iri owlInverseFunctionalProperty
  · have word : objectView t.object = .iri (characteristicWord 1#u8) := h4
    simp only [owlInverseFunctionalProperty] at h4
    simp only [h4, decide_true, ↓reduceIte] at ran
    exact characteristic_spec triples kinds index s t unused typed 1#u8 word r ran
  simp only [owlInverseFunctionalProperty] at h4
  simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h5 : objectView t.object = .iri owlReflexiveProperty
  · have word : objectView t.object = .iri (characteristicWord 2#u8) := h5
    simp only [owlReflexiveProperty] at h5
    simp only [h5, decide_true, ↓reduceIte] at ran
    exact characteristic_spec triples kinds index s t unused typed 2#u8 word r ran
  simp only [owlReflexiveProperty] at h5
  simp only [h5, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h6 : objectView t.object = .iri owlIrreflexiveProperty
  · have word : objectView t.object = .iri (characteristicWord 3#u8) := h6
    simp only [owlIrreflexiveProperty] at h6
    simp only [h6, decide_true, ↓reduceIte] at ran
    exact characteristic_spec triples kinds index s t unused typed 3#u8 word r ran
  simp only [owlIrreflexiveProperty] at h6
  simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h7 : objectView t.object = .iri owlSymmetricProperty
  · have word : objectView t.object = .iri (characteristicWord 4#u8) := h7
    simp only [owlSymmetricProperty] at h7
    simp only [h7, decide_true, ↓reduceIte] at ran
    exact characteristic_spec triples kinds index s t unused typed 4#u8 word r ran
  simp only [owlSymmetricProperty] at h7
  simp only [h7, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h8 : objectView t.object = .iri owlAsymmetricProperty
  · have word : objectView t.object = .iri (characteristicWord 5#u8) := h8
    simp only [owlAsymmetricProperty] at h8
    simp only [h8, decide_true, ↓reduceIte] at ran
    exact characteristic_spec triples kinds index s t unused typed 5#u8 word r ran
  simp only [owlAsymmetricProperty] at h8
  simp only [h8, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h9 : objectView t.object = .iri owlTransitiveProperty
  · have word : objectView t.object = .iri (characteristicWord 6#u8) := h9
    simp only [owlTransitiveProperty] at h9
    simp only [h9, decide_true, ↓reduceIte] at ran
    exact characteristic_spec triples kinds index s t unused typed 6#u8 word r ran
  simp only [owlTransitiveProperty] at h9
  simp only [h9, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h10 : objectView t.object = .iri owlAllDisjointClasses
  · have object := h10
    simp only [owlAllDisjointClasses] at h10
    simp only [h10, decide_true, ↓reduceIte] at ran
    exact all_disjoint_classes_spec triples kinds index s fuel t unused typed object r ran
  simp only [owlAllDisjointClasses] at h10
  simp only [h10, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h11 : objectView t.object = .iri owlAllDisjointProperties
  · have object := h11
    simp only [owlAllDisjointProperties] at h11
    simp only [h11, decide_true, ↓reduceIte] at ran
    exact all_disjoint_properties_spec triples kinds index s fuel t unused typed object r ran
  simp only [owlAllDisjointProperties] at h11
  simp only [h11, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h12 : objectView t.object = .iri owlAllDifferent
  · have object := h12
    simp only [owlAllDifferent] at h12
    simp only [h12, decide_true, ↓reduceIte] at ran
    exact all_different_spec triples index s fuel t unused typed object r ran
  simp only [owlAllDifferent] at h12
  simp only [h12, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases h13 : objectView t.object = .iri owlNegativePropertyAssertion
  · have object := h13
    simp only [owlNegativePropertyAssertion] at h13
    simp only [h13, decide_true, ↓reduceIte] at ran
    exact negative_assertion_spec triples kinds index s t unused typed object r ran
  simp only [owlNegativePropertyAssertion] at h13
  simp only [h13, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  obtain ⟨b, -, ran⟩ := bind_eq_ok ran
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at ran
    exact class_assertion_spec triples kinds index s fuel t unused typed r ran
  · simp at ran; subst ran; trivial

theorem read_axiom_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (index : Usize) (s : rdf_mapping.State) (fuel : Usize) (t : rdf.Triple)
    (unused : Unused triples.val s.used.val index.val t) (r : rdf_mapping.Read)
    (ran : rdf_mapping.read_axiom triples kinds index s fuel = .ok r) : ReadOk triples s r := by
  rw [rdf_mapping.read_axiom] at ran
  simp only [alloc.vec.Vec.index_slice_index, main_lookup triples index t unused.1, lift, bind_ok,
    same_correct] at ran
  repeat rw [slice_val] at ran
  by_cases p0 : t.predicate.spelling.val = rdfType
  · have spelled := p0
    simp only [rdfType] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact typing_spec triples kinds index s fuel t unused p0 r ran
  simp only [rdfType] at p0
  simp only [p0, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p1 : t.predicate.spelling.val = rdfsSubClassOf
  · have spelled := p1
    simp only [rdfsSubClassOf] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact sub_class_spec triples kinds index s fuel t unused p1 r ran
  simp only [rdfsSubClassOf] at p1
  simp only [p1, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p2 : t.predicate.spelling.val = owlEquivalentClass
  · have spelled := p2
    simp only [owlEquivalentClass] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact equivalent_class_spec triples kinds index s fuel t unused p2 r ran
  simp only [owlEquivalentClass] at p2
  simp only [p2, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p3 : t.predicate.spelling.val = owlDisjointWith
  · have spelled := p3
    simp only [owlDisjointWith] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact disjoint_class_spec triples kinds index s fuel t unused p3 r ran
  simp only [owlDisjointWith] at p3
  simp only [p3, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p4 : t.predicate.spelling.val = owlDisjointUnionOf
  · have spelled := p4
    simp only [owlDisjointUnionOf] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact disjoint_union_spec triples kinds index s fuel t unused p4 r ran
  simp only [owlDisjointUnionOf] at p4
  simp only [p4, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p5 : t.predicate.spelling.val = rdfsSubPropertyOf
  · have spelled := p5
    simp only [rdfsSubPropertyOf] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact sub_property_spec triples kinds index s t unused p5 r ran
  simp only [rdfsSubPropertyOf] at p5
  simp only [p5, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p6 : t.predicate.spelling.val = owlPropertyChainAxiom
  · have spelled := p6
    simp only [owlPropertyChainAxiom] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact property_chain_spec triples kinds index s fuel t unused p6 r ran
  simp only [owlPropertyChainAxiom] at p6
  simp only [p6, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p7 : t.predicate.spelling.val = owlEquivalentProperty
  · have spelled := p7
    simp only [owlEquivalentProperty] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact equivalent_property_spec triples kinds index s t unused p7 r ran
  simp only [owlEquivalentProperty] at p7
  simp only [p7, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p8 : t.predicate.spelling.val = owlPropertyDisjointWith
  · have spelled := p8
    simp only [owlPropertyDisjointWith] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact disjoint_property_spec triples kinds index s t unused p8 r ran
  simp only [owlPropertyDisjointWith] at p8
  simp only [p8, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p9 : t.predicate.spelling.val = owlInverseOf
  · have spelled := p9
    simp only [owlInverseOf] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact inverse_properties_spec triples index s t unused p9 r ran
  simp only [owlInverseOf] at p9
  simp only [p9, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p10 : t.predicate.spelling.val = rdfsDomain
  · have spelled := p10
    simp only [rdfsDomain] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact domain_spec triples kinds index s fuel t unused p10 r ran
  simp only [rdfsDomain] at p10
  simp only [p10, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p11 : t.predicate.spelling.val = rdfsRange
  · have spelled := p11
    simp only [rdfsRange] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact range_spec triples kinds index s fuel t unused p11 r ran
  simp only [rdfsRange] at p11
  simp only [p11, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p12 : t.predicate.spelling.val = owlSameAs
  · have spelled := p12
    simp only [owlSameAs] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact same_individual_spec triples index s t unused p12 r ran
  simp only [owlSameAs] at p12
  simp only [p12, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p13 : t.predicate.spelling.val = owlDifferentFrom
  · have spelled := p13
    simp only [owlDifferentFrom] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact different_individuals_spec triples index s t unused p13 r ran
  simp only [owlDifferentFrom] at p13
  simp only [p13, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  by_cases p14 : t.predicate.spelling.val = owlHasKey
  · have spelled := p14
    simp only [owlHasKey] at spelled
    simp only [spelled, decide_true, ↓reduceIte] at ran
    exact has_key_spec triples kinds index s fuel t unused p14 r ran
  simp only [owlHasKey] at p14
  simp only [p14, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
  obtain ⟨b, -, ran⟩ := bind_eq_ok ran
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at ran
    exact assertion_spec triples kinds index s t unused r ran
  · simp at ran; subst ran; exact grows_refl _ _

theorem axioms_from_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (out axioms : alloc.vec.Vec model.AnnotatedAxiom),
      rdf_mapping.axioms_from triples kinds index s out = .ok (some (axioms, s')) →
      ∃ news patterns fresh, axioms.val = out.val ++ news ∧ Grows triples.val s s' patterns fresh ∧
        ∀ rest, TAxioms news (fresh ++ rest) patterns rest := by
  intro index
  induction h : triples.val.length - index.val generalizing index with
  | zero =>
    intro s s' out axioms ran
    rw [rdf_mapping.axioms_from] at ran
    have done : ¬ index.val < triples.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨[], [], [], by simp, grows_refl _ _, fun rest => .nil rest⟩
  | succ n ih =>
    intro s s' out axioms ran
    rw [rdf_mapping.axioms_from] at ran
    have more : index.val < triples.val.length := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok] at ran
    by_cases isUsed : s.used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      obtain ⟨r, readRun, ran⟩ := bind_eq_ok ran
      have unused : Unused triples.val s.used.val index.val triples.val[index.val] :=
        ⟨List.getElem?_eq_getElem more, isUsed⟩
      have readOk := read_axiom_spec triples kinds index s _ _ unused r readRun
      cases r with
      | Fail => simp at ran
      | Skip s1 =>
        simp only [advance, bind_ok] at ran
        have g : Grows triples.val s s1 [] [] := readOk
        obtain ⟨news, patterns, fresh, split, grows, axioms'⟩ := ih next (by omega) s1 s' out axioms ran
        exact ⟨news, patterns, fresh, split, by simpa using grows_trans g grows, axioms'⟩
      | Found a s1 =>
        obtain ⟨p1, f1, g, ta⟩ := readOk
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec out { annotations := alloc.vec.Vec.new _, «axiom» := a } room)
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance] at ran
          obtain ⟨news, patterns, fresh, split, grows, axioms'⟩ := ih next (by omega) s1 s' pushed axioms ran
          refine ⟨{ annotations := alloc.vec.Vec.new _, «axiom» := a } :: news, p1 ++ patterns, f1 ++ fresh,
            by rw [split, contents]; simp, grows_trans g grows, fun rest => ?_⟩
          rw [List.append_assoc]
          exact .cons _ news _ _ _ p1 patterns rfl (ta _) (axioms' rest)
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, advance, bind_ok] at ran
      exact ih next (by omega) s s' out axioms ran

/-! ### Declarations -/

theorem copy_kind_identity (kind : typing.EntityKind) : rdf_mapping.copy_kind kind = .ok kind := by
  cases kind <;> rfl

theorem entity_of_spec (object : rdf.Object) (kind : typing.EntityKind)
    (kindRun : rdf_mapping.declaration_kind object = .ok (some kind)) (spelling : alloc.vec.Vec U8) :
    ∃ e, rdf_mapping.entity_of kind spelling = .ok e ∧
      declarationPattern e = ⟨.iri spelling.val, rdfType, objectView object⟩ := by
  rw [rdf_mapping.declaration_kind] at kindRun
  simp only [lift, bind_ok, object_is_correct] at kindRun
  repeat rw [slice_val] at kindRun
  by_cases c0 : objectView object = .iri owlClass
  · have c' := c0
    simp only [owlClass] at c'
    simp only [c', decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at kindRun
    subst kindRun
    exact ⟨.Class ⟨⟨spelling⟩⟩, by simp [rdf_mapping.entity_of, iri_of_identity],
      by simp [declarationPattern, iriNode, c0]⟩
  simp only [owlClass] at c0
  simp only [c0, decide_false, Bool.false_eq_true, ↓reduceIte] at kindRun
  by_cases c1 : objectView object = .iri rdfsDatatype
  · have c' := c1
    simp only [rdfsDatatype] at c'
    simp only [c', decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at kindRun
    subst kindRun
    exact ⟨.Datatype ⟨⟨spelling⟩⟩, by simp [rdf_mapping.entity_of, iri_of_identity],
      by simp [declarationPattern, iriNode, c1]⟩
  simp only [rdfsDatatype] at c1
  simp only [c1, decide_false, Bool.false_eq_true, ↓reduceIte] at kindRun
  by_cases c2 : objectView object = .iri owlObjectProperty
  · have c' := c2
    simp only [owlObjectProperty] at c'
    simp only [c', decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at kindRun
    subst kindRun
    exact ⟨.ObjectProperty ⟨⟨spelling⟩⟩, by simp [rdf_mapping.entity_of, iri_of_identity],
      by simp [declarationPattern, iriNode, c2]⟩
  simp only [owlObjectProperty] at c2
  simp only [c2, decide_false, Bool.false_eq_true, ↓reduceIte] at kindRun
  by_cases c3 : objectView object = .iri owlDatatypeProperty
  · have c' := c3
    simp only [owlDatatypeProperty] at c'
    simp only [c', decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at kindRun
    subst kindRun
    exact ⟨.DataProperty ⟨⟨spelling⟩⟩, by simp [rdf_mapping.entity_of, iri_of_identity],
      by simp [declarationPattern, iriNode, c3]⟩
  simp only [owlDatatypeProperty] at c3
  simp only [c3, decide_false, Bool.false_eq_true, ↓reduceIte] at kindRun
  by_cases c4 : objectView object = .iri owlAnnotationProperty
  · have c' := c4
    simp only [owlAnnotationProperty] at c'
    simp only [c', decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at kindRun
    subst kindRun
    exact ⟨.AnnotationProperty ⟨⟨spelling⟩⟩, by simp [rdf_mapping.entity_of, iri_of_identity],
      by simp [declarationPattern, iriNode, c4]⟩
  simp only [owlAnnotationProperty] at c4
  simp only [c4, decide_false, Bool.false_eq_true, ↓reduceIte] at kindRun
  by_cases c5 : objectView object = .iri owlNamedIndividual
  · have c' := c5
    simp only [owlNamedIndividual] at c'
    simp only [c', decide_true, ↓reduceIte, Result.ok.injEq, Option.some.injEq] at kindRun
    subst kindRun
    exact ⟨.NamedIndividual ⟨⟨spelling⟩⟩, by simp [rdf_mapping.entity_of, iri_of_identity],
      by simp [declarationPattern, iriNode, c5]⟩
  simp only [owlNamedIndividual] at c5
  simp only [c5, decide_false, Bool.false_eq_true, ↓reduceIte] at kindRun
  simp at kindRun

theorem declarations_spec (triples : alloc.vec.Vec rdf.Triple) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (axioms axioms' : alloc.vec.Vec model.AnnotatedAxiom)
      (kinds kinds' : alloc.vec.Vec rdf_mapping.Declared),
      rdf_mapping.declarations triples index s axioms kinds = .ok (some (axioms', kinds', s')) →
      (∀ (j : Nat), index.val ≤ j → j < triples.val.length → s.used.val[j]? = some false) →
      ∃ news patterns, axioms'.val = axioms.val ++ news ∧ Grows triples.val s s' patterns [] ∧
        ∀ rest, TAxioms news rest patterns rest := by
  intro index
  induction h : triples.val.length - index.val generalizing index with
  | zero =>
    intro s s' axioms axioms' kinds kinds' ran fresh
    rw [rdf_mapping.declarations] at ran
    have done : ¬ index.val < triples.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl, rfl⟩ := ran
    exact ⟨[], [], by simp, grows_refl _ _, fun rest => .nil rest⟩
  | succ n ih =>
    intro s s' axioms axioms' kinds kinds' ran fresh
    rw [rdf_mapping.declarations] at ran
    have more : index.val < triples.val.length := by omega
    obtain ⟨t, at_t⟩ : ∃ t, triples.val[index.val]? = some t := ⟨_, List.getElem?_eq_getElem more⟩
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      main_lookup triples index t at_t, lift, bind_ok, same_correct] at ran
    repeat rw [slice_val] at ran
    obtain ⟨declared, declaredRun, ran⟩ := bind_eq_ok ran
    cases declared with
    | none =>
      simp only [advance, bind_ok] at ran
      exact ih next (by omega) s s' axioms axioms' kinds kinds' ran (fun j low high => fresh j (by omega) high)
    | some p =>
      obtain ⟨spelling, kind⟩ := p
      have found : ∃ iri, t.subject = .Iri iri ∧ spelling = iri.spelling ∧ t.predicate.spelling.val = rdfType ∧
          rdf_mapping.declaration_kind t.object = .ok (some kind) := by
        by_cases typed : t.predicate.spelling.val = rdfType
        · have typed' := typed
          simp only [rdfType] at typed'
          simp only [typed', decide_true, ↓reduceIte] at declaredRun
          cases subject : t.subject with
          | Blank _ => simp [subject] at declaredRun
          | Iri iri =>
            simp only [subject] at declaredRun
            obtain ⟨o, kindRun, declaredRun⟩ := bind_eq_ok declaredRun
            cases o with
            | none => simp at declaredRun
            | some k =>
              simp [Rowl.Nnf.copy_bytes_identity] at declaredRun
              obtain ⟨rfl, rfl⟩ := declaredRun
              exact ⟨iri, rfl, rfl, typed, kindRun⟩
        · simp only [rdfType] at typed
          simp [typed] at declaredRun
      obtain ⟨iri, subject, rfl, typed, kindRun⟩ := found
      obtain ⟨e, entityRun, pattern⟩ := entity_of_spec _ kind kindRun iri.spelling
      by_cases room1 : axioms.val.length < Usize.max
      · by_cases room2 : kinds.val.length < Usize.max
        · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec axioms { annotations := alloc.vec.Vec.new _, «axiom» := .Declaration e } room1)
          obtain ⟨pushedK, pushK, -⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec kinds { iri := iri.spelling, kind := kind } room2)
          simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room1, room2, entityRun, push,
            copy_kind_identity, pushK, advance, take_correct] at ran
          have unused : Unused triples.val s.used.val index.val t := ⟨at_t, fresh index.val (le_refl _) more⟩
          have g0 := take_main triples s index t unused
          rw [subject, typed] at g0
          have g1 : Grows triples.val s { s with used := s.used.set index true } [declarationPattern e] [] := by
            rw [pattern]
            exact g0
          obtain ⟨news, patterns, split, grows, decls⟩ := ih next (by omega) _ s' pushed axioms' pushedK kinds' ran
            (fun j low high => by
              simp only [alloc.vec.Vec.set_val_eq]
              rw [List.getElem?_set_ne (by omega)]
              exact fresh j (by omega) high)
          refine ⟨{ annotations := alloc.vec.Vec.new _, «axiom» := .Declaration e } :: news,
            declarationPattern e :: patterns, by rw [split, contents]; simp, by simpa using grows_trans g1 grows,
            fun rest => ?_⟩
          exact .cons _ news rest rest rest [declarationPattern e] patterns rfl (TAxiom.declaration e rest) (decls rest)
        · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room1, room2] at ran
      · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room1] at ran

/-! ### The ontology header -/

theorem find_header_spec (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (index found : Usize)
    (ran : rdf_mapping.find_header triples used index = .ok (some found)) :
    ∃ t, Unused triples.val used.val found.val t ∧ t.predicate.spelling.val = rdfType ∧
      objectView t.object = .iri owlOntology ∧ ∃ iri, t.subject = .Iri iri := by
  rw [rdf_mapping.find_header] at ran
  by_cases more : index.val < triples.val.length
  · have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, same_correct, object_is_correct, advance, lift] at ran
    repeat rw [slice_val] at ran
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      by_cases typed : triples.val[index.val].predicate.spelling.val = rdfType
      · have typed' := typed
        simp only [rdfType] at typed'
        simp only [typed', decide_true, ↓reduceIte] at ran
        by_cases onto : objectView triples.val[index.val].object = .iri owlOntology
        · have onto' := onto
          simp only [owlOntology] at onto'
          simp only [onto', decide_true, ↓reduceIte] at ran
          cases subject : triples.val[index.val].subject with
          | Iri iri =>
            simp only [subject, Result.ok.injEq, Option.some.injEq] at ran
            subst ran
            exact ⟨_, ⟨List.getElem?_eq_getElem more, isUsed⟩, typed, onto, iri, subject⟩
          | Blank _ =>
            simp only [subject] at ran
            exact find_header_spec triples used next found ran
        · simp only [owlOntology] at onto
          simp only [onto, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
          exact find_header_spec triples used next found ran
      · simp only [rdfType] at typed
        simp only [typed, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
        exact find_header_spec triples used next found ran
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at ran
      exact find_header_spec triples used next found ran
  · simp [UScalar.lt_equiv, more] at ran
termination_by triples.val.length - index.val
decreasing_by all_goals (have := nextValue; simp at this; omega)

theorem about_iri_spec (t : rdf.Triple) (ontology : alloc.vec.Vec U8)
    (ran : rdf_mapping.about_iri t ontology = .ok true) : subjectView t.subject = .iri ontology.val := by
  rw [rdf_mapping.about_iri] at ran
  cases subject : t.subject with
  | Blank _ => simp [subject] at ran
  | Iri iri =>
    simp [subject, same_vec_correct] at ran
    simp [subjectView, ran]

/-- The `owl:versionIRI` triple a header read adds: one when it finds the
    first version IRI. -/
def versionPatterns (ontology : Node) : Option model.Iri → Option model.Iri → List Pattern
  | none, some v => [⟨ontology, owlVersionIRI, iriNode v⟩]
  | _, _ => []

theorem header_parts_spec (triples : alloc.vec.Vec rdf.Triple) (kinds : alloc.vec.Vec rdf_mapping.Declared)
    (ontology : alloc.vec.Vec U8) :
    ∀ (index : Usize) (s s' : rdf_mapping.State) (version version' : Option model.Iri)
      (imports imports' : alloc.vec.Vec model.Iri) (annotations annotations' : alloc.vec.Vec model.Annotation),
      rdf_mapping.header_parts triples kinds ontology index s version imports annotations =
        .ok (some (version', imports', annotations', s')) →
      ∃ newImports newAnnotations annotationPatterns,
        imports'.val = imports.val ++ newImports ∧ annotations'.val = annotations.val ++ newAnnotations ∧
        (version.isSome → version' = version) ∧
        List.Forall₂ (TAnnotation (.iri ontology.val)) newAnnotations annotationPatterns ∧
        Grows triples.val s s' (versionPatterns (.iri ontology.val) version version' ++
          newImports.map (fun i => ⟨.iri ontology.val, owlImports, iriNode i⟩) ++ annotationPatterns) [] := by
  intro index
  induction h : triples.val.length - index.val generalizing index with
  | zero =>
    intro s s' version version' imports imports' annotations annotations' ran
    rw [rdf_mapping.header_parts] at ran
    have done : ¬ index.val < triples.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ran
    refine ⟨[], [], [], by simp, by simp, fun _ => rfl, .nil, ?_⟩
    cases version <;> simpa [versionPatterns] using grows_refl triples.val s
  | succ n ih =>
    intro s s' version version' imports imports' annotations annotations' ran
    rw [rdf_mapping.header_parts] at ran
    have more : index.val < triples.val.length := by omega
    obtain ⟨t, at_t⟩ : ∃ t, triples.val[index.val]? = some t := ⟨_, List.getElem?_eq_getElem more⟩
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, main_lookup triples index t at_t, lift, same_correct] at ran
    repeat rw [slice_val] at ran
    by_cases isUsed : s.used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      obtain ⟨about, aboutRun, ran⟩ := bind_eq_ok ran
      cases about with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, advance, bind_ok] at ran
        exact ih next (by omega) s s' version version' imports imports' annotations annotations' ran
      | true =>
        simp only [↓reduceIte] at ran
        have g0 := take_main triples s index t ⟨at_t, isUsed⟩
        rw [about_iri_spec t ontology aboutRun] at g0
        by_cases isVersion : t.predicate.spelling.val = owlVersionIRI
        · have isVersion' := isVersion
          simp only [owlVersionIRI] at isVersion'
          simp only [isVersion', decide_true, ↓reduceIte] at ran
          cases version with
          | some _ => simp at ran
          | none =>
            simp only at ran
            obtain ⟨o, iriRun, ran⟩ := bind_eq_ok ran
            cases o with
            | none => simp at ran
            | some v =>
              simp only [advance, take_correct, bind_ok] at ran
              obtain ⟨newImports, newAnnotations, annotationPatterns, splitI, splitA, keep, forall2, grows⟩ :=
                ih next (by omega) _ s' (some v) version' imports imports' annotations annotations' ran
              have versionIs := keep rfl
              subst versionIs
              rw [isVersion, node_iri_spec _ v iriRun] at g0
              refine ⟨newImports, newAnnotations, annotationPatterns, splitI, splitA, fun known => by simp at known,
                forall2, ?_⟩
              simpa [versionPatterns] using grows_trans g0 grows
        · simp only [owlVersionIRI] at isVersion
          simp only [isVersion, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
          by_cases isImport : t.predicate.spelling.val = owlImports
          · have isImport' := isImport
            simp only [owlImports] at isImport'
            simp only [isImport', decide_true, ↓reduceIte] at ran
            obtain ⟨o, iriRun, ran⟩ := bind_eq_ok ran
            cases o with
            | none => simp at ran
            | some iri =>
              simp only at ran
              by_cases room : imports.val.length < Usize.max
              · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec imports iri room)
                simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, push, advance, take_correct] at ran
                obtain ⟨newImports, newAnnotations, annotationPatterns, splitI, splitA, keep, forall2, grows⟩ :=
                  ih next (by omega) _ s' version version' pushed imports' annotations annotations' ran
                rw [isImport, node_iri_spec _ iri iriRun] at g0
                refine ⟨iri :: newImports, newAnnotations, annotationPatterns, by rw [splitI, contents]; simp, splitA,
                  keep, forall2, grows_same (grows_trans g0 grows) ?_⟩
                intro x
                simp only [List.mem_cons, List.mem_append, List.map_cons, List.not_mem_nil, or_false]
                tauto
              · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran
          · simp only [owlImports] at isImport
            simp only [isImport, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
            obtain ⟨o, kindRun, ran⟩ := bind_eq_ok ran
            cases o with
            | none =>
              simp only [advance, bind_ok] at ran
              exact ih next (by omega) s s' version version' imports imports' annotations annotations' ran
            | some pk =>
              cases pk with
              | Object =>
                simp only [advance, bind_ok] at ran
                exact ih next (by omega) s s' version version' imports imports' annotations annotations' ran
              | Data =>
                simp only [advance, bind_ok] at ran
                exact ih next (by omega) s s' version version' imports imports' annotations annotations' ran
              | Annotation =>
                simp only at ran
                obtain ⟨o1, valueRun, ran⟩ := bind_eq_ok ran
                cases o1 with
                | none => simp at ran
                | some value =>
                  simp only at ran
                  by_cases room : annotations.val.length < Usize.max
                  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec annotations
                      (model.Annotation.mk (alloc.vec.Vec.new _) ⟨⟨t.predicate.spelling⟩⟩ value) room)
                    simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, iri_of_identity, push, advance,
                      take_correct] at ran
                    obtain ⟨newImports, newAnnotations, annotationPatterns, splitI, splitA, keep, forall2, grows⟩ :=
                      ih next (by omega) _ s' version version' imports imports' pushed annotations' ran
                    refine ⟨newImports, model.Annotation.mk (alloc.vec.Vec.new _) ⟨⟨t.predicate.spelling⟩⟩ value ::
                        newAnnotations, ⟨.iri ontology.val, t.predicate.spelling.val, objectView t.object⟩ ::
                        annotationPatterns, splitI, by rw [splitA, contents]; simp, keep,
                      .cons (TAnnotation.mk _ _ rfl (annotation_value_spec _ value valueRun)) forall2,
                      grows_same (grows_trans g0 grows) ?_⟩
                    intro x
                    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
                    tauto
                  · simp [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room] at ran
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, advance, bind_ok] at ran
      exact ih next (by omega) s s' version version' imports imports' annotations annotations' ran

/-! ### Reading every triple -/

theorem repeats_used_spec (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) (triple : rdf.Triple) :
    ∀ (index : Usize), rdf_mapping.repeats_used triples used triple index = .ok true →
      ∃ (j : Nat), triples.val[j]? = some triple ∧ used.val[j]? ≠ some false := by
  intro index
  induction h : triples.val.length - index.val generalizing index with
  | zero =>
    intro ran
    rw [rdf_mapping.repeats_used] at ran
    have done : ¬ index.val < triples.val.length := by omega
    simp [UScalar.lt_equiv, done] at ran
  | succ n ih =>
    intro ran
    rw [rdf_mapping.repeats_used] at ran
    have more : index.val < triples.val.length := by omega
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, same_triple_correct, advance] at ran
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      exact ih next (by omega) ran
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at ran
      by_cases same : triples.val[index.val] = triple
      · exact ⟨index.val, by rw [List.getElem?_eq_getElem more, same], isUsed⟩
      · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
        exact ih next (by omega) ran

theorem all_read_spec (triples : alloc.vec.Vec rdf.Triple) (used : alloc.vec.Vec Bool) :
    ∀ (index : Usize), rdf_mapping.all_read triples used index = .ok true →
      ∀ (i : Nat), index.val ≤ i → ∀ t, triples.val[i]? = some t →
        ∃ (j : Nat), triples.val[j]? = some t ∧ used.val[j]? ≠ some false := by
  intro index
  induction h : triples.val.length - index.val generalizing index with
  | zero =>
    intro ran i low t at_i
    have beyond : triples.val.length ≤ i := by omega
    simp [List.getElem?_eq_none beyond] at at_i
  | succ n ih =>
    intro ran i low t at_i
    rw [rdf_mapping.all_read] at ran
    have more : index.val < triples.val.length := by omega
    have lookup : triples.index_usize index = .ok triples.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, is_used_correct, bind_ok,
      alloc.vec.Vec.index_slice_index, lookup, advance] at ran
    by_cases isUsed : used.val[index.val]? = some false
    · simp only [isUsed, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ran
      obtain ⟨b, repeatsRun, ran⟩ := bind_eq_ok ran
      cases b with
      | false => simp at ran
      | true =>
        simp only [↓reduceIte, advance, bind_ok] at ran
        by_cases here : i = index.val
        · subst here
          rw [List.getElem?_eq_getElem more] at at_i
          cases at_i
          exact repeats_used_spec triples used _ 0#usize repeatsRun
        · exact ih next (by omega) ran i (by omega) t at_i
    · simp only [isUsed, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, advance, bind_ok] at ran
      by_cases here : i = index.val
      · subst here
        exact ⟨index.val, at_i, isUsed⟩
      · exact ih next (by omega) ran i (by omega) t at_i

theorem unused_spec (count : Usize) :
    ∀ (out v : alloc.vec.Vec Bool), rdf_mapping.unused count out = .ok v →
      v.val = out.val ++ List.replicate (count.val - out.val.length) false := by
  intro out
  induction h : count.val - out.val.length generalizing out with
  | zero =>
    intro v ran
    rw [rdf_mapping.unused] at ran
    have done : ¬ out.val.length < count.val := by omega
    simp [UScalar.lt_equiv, done] at ran
    subst ran
    simp
  | succ n ih =>
    intro v ran
    rw [rdf_mapping.unused] at ran
    have more : out.val.length < count.val := by omega
    have room : out.val.length < Usize.max := by scalar_tac
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out false room)
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, more, ↓reduceIte, push, bind_ok] at ran
    have rest := ih pushed (by rw [contents]; simp; omega) v ran
    rw [rest, contents, List.replicate_succ]
    simp

theorem taxioms_append {xs ys : List model.AnnotatedAxiom} {s s1 s2 : Supply} {p q : List Pattern}
    (first : TAxioms xs s p s1) (second : TAxioms ys s1 q s2) : TAxioms (xs ++ ys) s (p ++ q) s2 := by
  induction first with
  | nil => simpa using second
  | cons a rest s0 s1' s2' p' q' empty head tail ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons a (rest ++ ys) s0 s1' s2 p' (q' ++ q) empty head (ih second)

/-- A read of the graph from the state with no triple read that ends with every
    triple read, or repeating one that was, meets exactly the triples of the
    graph. -/
theorem read_all (triples : alloc.vec.Vec rdf.Triple) (s s' : rdf_mapping.State) (patterns : List Pattern)
    (fresh : List rdf.BlankNode) (start : ∀ (j : Nat), j < triples.val.length → s.used.val[j]? = some false)
    (grows : Grows triples.val s s' patterns fresh)
    (allRun : rdf_mapping.all_read triples s'.used 0#usize = .ok true) :
    (∀ t ∈ triples.val, ∃ p ∈ patterns, Matches p t) ∧ (∀ p ∈ patterns, ∃ t ∈ triples.val, Matches p t) := by
  constructor
  · intro t member
    obtain ⟨i, at_i⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨j, at_j, usedJ⟩ := all_read_spec triples s'.used 0#usize allRun i (Nat.zero_le _) t at_i
    have inside : j < triples.val.length := (List.getElem?_eq_some_iff.mp at_j).1
    have before := start j inside
    have inside' : j < s'.used.val.length := by
      rw [grows.length]
      exact (List.getElem?_eq_some_iff.mp before).1
    have after : s'.used.val[j]? = some true := by
      cases value : s'.used.val[j]'inside' with
      | true => rw [List.getElem?_eq_getElem inside', value]
      | false => exact absurd (by rw [List.getElem?_eq_getElem inside', value]) usedJ
    obtain ⟨t', at_t', p, member', fits⟩ := grows.sound j before after
    rw [at_j] at at_t'
    cases at_t'
    exact ⟨p, member', fits⟩
  · intro p member
    obtain ⟨i, t, -, -, at_i, fits⟩ := grows.complete p member
    exact ⟨t, List.mem_iff_getElem?.mpr ⟨i, at_i⟩, fits⟩

/-! ### The mapping of a graph -/

/-- **The RDF mapping reads graphs back exactly.** Whenever `map_graph` returns
    an ontology, the forward mapping of that ontology, allocating exactly the
    blank nodes it returns, gives the triples of the input graph: every triple
    instantiates one of its patterns and every pattern is instantiated by a
    triple of the graph. -/
theorem map_graph_correct (graph : rdf.RawGraph) (m : rdf_mapping.Mapped)
    (ran : rdf_mapping.map_graph graph = .ok (some m)) :
    ∃ patterns, TOntology m.ontology m.blanks.val patterns ∧
      (∀ t ∈ graph.triples.val, ∃ p ∈ patterns, Matches p t) ∧
      (∀ p ∈ patterns, ∃ t ∈ graph.triples.val, Matches p t) := by
  rw [rdf_mapping.map_graph] at ran
  obtain ⟨v, unusedRun, ran⟩ := bind_eq_ok ran
  have vIs := unused_spec _ _ v unusedRun
  simp at vIs
  have start : ∀ (j : Nat), j < graph.triples.val.length →
      (({ used := v, blanks := alloc.vec.Vec.new rdf.BlankNode } : rdf_mapping.State).used.val[j]? = some false) := by
    intro j inside
    simp [vIs, List.getElem?_replicate, inside]
  obtain ⟨o, declarationsRun, ran⟩ := bind_eq_ok ran
  cases o with
  | none => simp at ran
  | some p =>
    obtain ⟨axioms, kinds, s1⟩ := p
    obtain ⟨decls, declPatterns, declSplit, declGrows, declAxioms⟩ := declarations_spec graph.triples 0#usize _ s1 _
      axioms _ kinds declarationsRun (fun j _ inside => start j inside)
    simp at declSplit
    have noBlanks : s1.blanks.val = [] := by
      rw [declGrows.blanks]
      simp
    obtain ⟨o1, headerRun, ran⟩ := bind_eq_ok ran
    cases o1 with
    | none =>
      obtain ⟨o2, axiomsRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p2 =>
        obtain ⟨axioms1, s2⟩ := p2
        obtain ⟨news, patterns2, fresh, split, grows2, axioms2⟩ := axioms_from_spec graph.triples kinds 0#usize s1 s2
          axioms axioms1 axiomsRun
        obtain ⟨b, readRun, ran⟩ := bind_eq_ok ran
        cases b with
        | false => simp at ran
        | true =>
          simp at ran
          subst ran
          have blanksIs : s2.blanks.val = fresh := by rw [grows2.blanks, noBlanks]; simp
          have whole := grows_trans declGrows grows2
          obtain ⟨cover, exact⟩ := read_all graph.triples _ s2 _ _ start whole readRun
          refine ⟨declPatterns ++ patterns2, ⟨[], declPatterns ++ patterns2, THeader.anonymous _ rfl rfl rfl, ?_, rfl⟩,
            cover, exact⟩
          show TAxioms axioms1.val s2.blanks.val (declPatterns ++ patterns2) []
          rw [split, declSplit, blanksIs]
          simpa using taxioms_append (declAxioms (fresh ++ [])) (axioms2 [])
    | some header =>
      obtain ⟨t, unusedH, typed, onto, iri, subjectH⟩ := find_header_spec graph.triples s1.used 0#usize header
        headerRun
      simp only [alloc.vec.Vec.index_slice_index, main_lookup graph.triples header t unusedH.1, bind_ok,
        subjectH] at ran
      simp only [take_correct, bind_ok] at ran
      have g0 := take_main graph.triples s1 header t unusedH
      rw [subjectH, typed, onto] at g0
      obtain ⟨o2, partsRun, ran⟩ := bind_eq_ok ran
      cases o2 with
      | none => simp at ran
      | some p2 =>
        obtain ⟨version, imports, annotations, s3⟩ := p2
        obtain ⟨newImports, newAnnotations, annotationPatterns, splitI, splitA, -, forall2, grows3⟩ :=
          header_parts_spec graph.triples kinds iri.spelling 0#usize _ s3 none version _ imports _ annotations partsRun
        simp at splitI splitA
        simp only [iri_of_identity, bind_ok] at ran
        obtain ⟨o3, axiomsRun, ran⟩ := bind_eq_ok ran
        cases o3 with
        | none => simp at ran
        | some p3 =>
          obtain ⟨axioms1, s4⟩ := p3
          obtain ⟨news, patterns2, fresh, split, grows2, axioms2⟩ := axioms_from_spec graph.triples kinds 0#usize s3 s4
            axioms axioms1 axiomsRun
          obtain ⟨b, readRun, ran⟩ := bind_eq_ok ran
          cases b with
          | false => simp at ran
          | true =>
            simp at ran
            subst ran
            have blanksIs : s4.blanks.val = fresh := by
              rw [grows2.blanks, grows3.blanks, g0.blanks, noBlanks]
              simp
            have forall2' : List.Forall₂ (TAnnotation (iriNode ⟨iri.spelling⟩)) annotations.val annotationPatterns := by
              rw [splitA]
              exact forall2
            obtain ⟨headerPatterns, header, headerIs⟩ : ∃ H, THeader
                { identity := .Named ⟨iri.spelling⟩ version, imports, annotations, axioms := axioms1 } H ∧
                ∀ x, x ∈ H ↔ x ∈ [⟨.iri iri.spelling.val, rdfType, .iri owlOntology⟩] ++
                  versionPatterns (.iri iri.spelling.val) none version ++
                  imports.val.map (fun i => ⟨.iri iri.spelling.val, owlImports, iriNode i⟩) ++ annotationPatterns := by
              cases version with
              | none =>
                exact ⟨_, THeader.named _ ⟨iri.spelling⟩ none annotationPatterns rfl forall2',
                  fun x => by simp [versionPatterns, iriNode]⟩
              | some v =>
                exact ⟨_, THeader.named _ ⟨iri.spelling⟩ (some v) annotationPatterns rfl forall2',
                  fun x => by simp [versionPatterns, iriNode]⟩
            have whole := grows_trans (grows_trans (grows_trans declGrows g0) grows3) grows2
            have same : ∀ x, x ∈ declPatterns ++ [⟨subjectView (.Iri iri), rdfType, .iri owlOntology⟩] ++
                (versionPatterns (.iri iri.spelling.val) none version ++
                  newImports.map (fun i => ⟨.iri iri.spelling.val, owlImports, iriNode i⟩) ++ annotationPatterns) ++
                patterns2 ↔ x ∈ headerPatterns ++ (declPatterns ++ patterns2) := by
              intro x
              simp only [List.mem_append, headerIs, splitI, subjectView, List.mem_cons, List.mem_singleton,
                List.not_mem_nil, or_false]
              tauto
            obtain ⟨cover, exact⟩ := read_all graph.triples _ s4 _ _ start (grows_same whole same) readRun
            refine ⟨headerPatterns ++ (declPatterns ++ patterns2), ⟨headerPatterns, declPatterns ++ patterns2, header, ?_,
              rfl⟩, cover, exact⟩
            show TAxioms axioms1.val s4.blanks.val (declPatterns ++ patterns2) []
            rw [split, declSplit, blanksIs]
            simpa using taxioms_append (declAxioms (fresh ++ [])) (axioms2 [])

end Rowl.RdfMapping
