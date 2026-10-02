//! Functional Syntax documents: the prefix declarations, the ontology header and
//! annotations, and every axiom up to the closing parenthesis and the end of the
//! source.
//!
//! The axiom loop dispatches on the axiom keyword to the proved declaration,
//! annotation-axiom, class-axiom and assertion readers. The other logical axiom
//! forms are reported as unsupported at their keyword; later stages read them.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal};
use crate::functional_annotation_axioms::{
    read_annotation_axiom, AnnotationAxiomError, SourceAnnotationAxiom,
};
use crate::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation,
};
use crate::functional_assertions::{read_assertion, AssertionError, SourceAssertion};
use crate::functional_class_axioms::{read_class_axiom, ClassAxiomError, SourceClassAxiom};
use crate::functional_classes::ClassLimits;
use crate::functional_declarations::{read_declaration, DeclarationError, SourceDeclaration};
use crate::functional_header::{
    read_header_tail, HeaderError, ImportReference, SourceOntologyIdentity,
};
use crate::functional_lexer::Tokens;
use crate::functional_prefixes::{read_prefix_header, PrefixReadError};
use crate::prefixes::{check, Check, Declaration, PrefixTable};

/// One axiom of the forms this stage reads.
pub enum SourceAxiom {
    Declaration(SourceDeclaration),
    Annotation(SourceAnnotationAxiom),
    Class(SourceClassAxiom),
    Assertion(SourceAssertion),
}
/// Everything after `Ontology(`: the identity, the imports, the ontology
/// annotations and the axioms in source order.
pub struct SourceDocumentTail {
    pub identity: SourceOntologyIdentity,
    pub imports: Vec<ImportReference>,
    pub annotations: Vec<SourceAnnotation>,
    pub axioms: Vec<SourceAxiom>,
}
/// A whole document: its original prefix declarations and everything after them.
pub struct SourceDocument {
    pub prefixes: Vec<Declaration>,
    pub tail: SourceDocumentTail,
}
/// `tokens`, `prefixes` and `prefix_value` bound the lexer and the prefix
/// declarations; `imports` and `iri` bound the header; `axioms` bounds the axiom
/// count; annotations and class expressions keep their own limits.
pub struct DocumentLimits {
    pub tokens: usize,
    pub prefixes: usize,
    pub prefix_value: usize,
    pub imports: usize,
    pub iri: usize,
    pub axioms: usize,
    pub annotations: AnnotationLimits,
    pub classes: ClassLimits,
}
#[derive(Clone, Copy)]
pub enum DocumentExpected {
    /// An axiom or the closing parenthesis of the ontology.
    Axiom,
    /// The closing parenthesis of the ontology.
    Close,
    /// The end of the source after the closing parenthesis.
    End,
}
/// The namespace-table check that rejected the prefix declarations.
#[derive(Clone, Copy)]
pub enum TableError {
    InvalidName,
    ReservedName,
    InvalidNamespace,
    Duplicate,
}
pub enum DocumentError {
    Prefix(PrefixReadError),
    Table(TableError),
    Header(HeaderError),
    Annotation(AnnotationError),
    Declaration(DeclarationError),
    AnnotationAxiom(AnnotationAxiomError),
    ClassAxiom(ClassAxiomError),
    Assertion(AssertionError),
    /// An axiom form that this stage does not read yet.
    UnsupportedAxiom {
        offset: usize,
    },
    AxiomLimit {
        offset: usize,
    },
    Expected {
        expected: DocumentExpected,
        offset: usize,
    },
}
#[derive(Clone, Copy)]
enum AxiomFamily {
    Declaration,
    Annotation,
    Class,
    Assertion,
    Unsupported,
}
fn axiom_family(terminal: Terminal) -> Option<AxiomFamily> {
    match terminal {
        Terminal::Keyword(Keyword::Declaration) => Some(AxiomFamily::Declaration),
        Terminal::Keyword(Keyword::AnnotationAssertion) => Some(AxiomFamily::Annotation),
        Terminal::Keyword(Keyword::SubAnnotationPropertyOf) => Some(AxiomFamily::Annotation),
        Terminal::Keyword(Keyword::AnnotationPropertyDomain) => Some(AxiomFamily::Annotation),
        Terminal::Keyword(Keyword::AnnotationPropertyRange) => Some(AxiomFamily::Annotation),
        Terminal::Keyword(Keyword::SubClassOf) => Some(AxiomFamily::Class),
        Terminal::Keyword(Keyword::EquivalentClasses) => Some(AxiomFamily::Class),
        Terminal::Keyword(Keyword::DisjointClasses) => Some(AxiomFamily::Class),
        Terminal::Keyword(Keyword::DisjointUnion) => Some(AxiomFamily::Class),
        Terminal::Keyword(Keyword::ObjectPropertyDomain) => Some(AxiomFamily::Class),
        Terminal::Keyword(Keyword::ObjectPropertyRange) => Some(AxiomFamily::Class),
        Terminal::Keyword(Keyword::SubObjectPropertyOf) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::EquivalentObjectProperties) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::DisjointObjectProperties) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::InverseObjectProperties) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::FunctionalObjectProperty) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::InverseFunctionalObjectProperty) => {
            Some(AxiomFamily::Unsupported)
        }
        Terminal::Keyword(Keyword::ReflexiveObjectProperty) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::IrreflexiveObjectProperty) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::SymmetricObjectProperty) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::AsymmetricObjectProperty) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::TransitiveObjectProperty) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::SubDataPropertyOf) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::EquivalentDataProperties) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::DisjointDataProperties) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::DataPropertyDomain) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::DataPropertyRange) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::FunctionalDataProperty) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::DatatypeDefinition) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::HasKey) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::SameIndividual) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::DifferentIndividuals) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::ClassAssertion) => Some(AxiomFamily::Assertion),
        Terminal::Keyword(Keyword::ObjectPropertyAssertion) => Some(AxiomFamily::Assertion),
        Terminal::Keyword(Keyword::NegativeObjectPropertyAssertion) => Some(AxiomFamily::Assertion),
        Terminal::Keyword(Keyword::DataPropertyAssertion) => Some(AxiomFamily::Unsupported),
        Terminal::Keyword(Keyword::NegativeDataPropertyAssertion) => Some(AxiomFamily::Unsupported),
        _ => None,
    }
}
fn closes(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Close)
}
/// Read one axiom of a supported family, starting at its keyword.
fn read_axiom(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    family: AxiomFamily,
    tokens: Tokens,
    offset: usize,
    limits: &DocumentLimits,
) -> Result<(SourceAxiom, Tokens), DocumentError> {
    match family {
        AxiomFamily::Declaration => {
            match read_declaration(table, bytes, tokens, &limits.annotations) {
                Ok((axiom, rest)) => Ok((SourceAxiom::Declaration(axiom), rest)),
                Err(error) => Err(DocumentError::Declaration(error)),
            }
        }
        AxiomFamily::Annotation => {
            match read_annotation_axiom(table, bytes, tokens, &limits.annotations) {
                Ok((axiom, rest)) => Ok((SourceAxiom::Annotation(axiom), rest)),
                Err(error) => Err(DocumentError::AnnotationAxiom(error)),
            }
        }
        AxiomFamily::Class => {
            match read_class_axiom(table, bytes, tokens, &limits.annotations, &limits.classes) {
                Ok((axiom, rest)) => Ok((SourceAxiom::Class(axiom), rest)),
                Err(error) => Err(DocumentError::ClassAxiom(error)),
            }
        }
        AxiomFamily::Assertion => {
            match read_assertion(table, bytes, tokens, &limits.annotations, &limits.classes) {
                Ok((axiom, rest)) => Ok((SourceAxiom::Assertion(axiom), rest)),
                Err(error) => Err(DocumentError::Assertion(error)),
            }
        }
        AxiomFamily::Unsupported => Err(DocumentError::UnsupportedAxiom { offset }),
    }
}
/// Read every axiom up to the closing parenthesis, which is left in place.
fn read_axioms(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut axioms: Vec<SourceAxiom>,
    limits: &DocumentLimits,
) -> Result<(Vec<SourceAxiom>, Tokens), DocumentError> {
    let (token, next) = match tokens {
        Tokens::Empty => {
            return Err(DocumentError::Expected {
                expected: DocumentExpected::Close,
                offset: bytes.len(),
            })
        }
        Tokens::Cons { token, next } => (token, next),
    };
    if closes(token.terminal) {
        return Ok((axioms, Tokens::Cons { token, next }));
    }
    let offset = token.start;
    let family = match axiom_family(token.terminal) {
        Some(family) => family,
        None => {
            return Err(DocumentError::Expected {
                expected: DocumentExpected::Axiom,
                offset,
            })
        }
    };
    if axioms.len() >= limits.axioms {
        return Err(DocumentError::AxiomLimit { offset });
    }
    let (axiom, rest) = match read_axiom(
        table,
        bytes,
        family,
        Tokens::Cons { token, next },
        offset,
        limits,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    axioms.push(axiom);
    read_axioms(table, bytes, rest, axioms, limits)
}
/// Read everything after `Ontology(`: the identity and imports, the ontology
/// annotations, every axiom, the closing parenthesis, and then require the end
/// of the source.
pub fn read_document_tail(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &DocumentLimits,
) -> Result<SourceDocumentTail, DocumentError> {
    let header = match read_header_tail(table, bytes, tokens, limits.imports, limits.iri) {
        Ok(value) => value,
        Err(error) => return Err(DocumentError::Header(error)),
    };
    let annotated = match read_annotations(table, bytes, header.remaining, &limits.annotations) {
        Ok(value) => value,
        Err(error) => return Err(DocumentError::Annotation(error)),
    };
    let (axioms, tokens) = match read_axioms(table, bytes, annotated.remaining, Vec::new(), limits)
    {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let after = match tokens {
        Tokens::Empty => {
            return Err(DocumentError::Expected {
                expected: DocumentExpected::Close,
                offset: bytes.len(),
            })
        }
        Tokens::Cons { next, .. } => *next,
    };
    match after {
        Tokens::Empty => Ok(SourceDocumentTail {
            identity: header.identity,
            imports: header.imports,
            annotations: annotated.annotations,
            axioms,
        }),
        Tokens::Cons { token, .. } => Err(DocumentError::Expected {
            expected: DocumentExpected::End,
            offset: token.start,
        }),
    }
}
fn table_error(check: &Check<'_>) -> TableError {
    match check {
        Check::InvalidName(_) => TableError::InvalidName,
        Check::ReservedName(_) => TableError::ReservedName,
        Check::InvalidNamespace(_) => TableError::InvalidNamespace,
        _ => TableError::Duplicate,
    }
}
/// Read a whole Functional Syntax document from its original bytes: the prefix
/// declarations, which must form a normative namespace table, then everything
/// after `Ontology(` as `read_document_tail` describes. Every stage is a proved
/// reader; the first failing stage reports its error.
pub fn read_document(
    bytes: &Vec<u8>,
    limits: &DocumentLimits,
) -> Result<SourceDocument, DocumentError> {
    let prefix =
        match read_prefix_header(bytes, limits.tokens, limits.prefixes, limits.prefix_value) {
            Ok(value) => value,
            Err(error) => return Err(DocumentError::Prefix(error)),
        };
    let checked = check(&prefix.declarations);
    let tail = match checked {
        Check::Ready(table) => read_document_tail(&table, bytes, prefix.remaining, limits),
        other => Err(DocumentError::Table(table_error(&other))),
    };
    match tail {
        Ok(tail) => Ok(SourceDocument {
            prefixes: prefix.declarations,
            tail,
        }),
        Err(error) => Err(error),
    }
}
