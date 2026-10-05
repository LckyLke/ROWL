//! Classification of named classes: for every pair of the given classes,
//! whether every instance of the first is an instance of the second, and for
//! every class whether it can have an instance.
//!
//! Every answer is a proved prepared query's answer or follows from earlier
//! answers by the meaning of subsumption. A class without instances is
//! subsumed by every class, and a class with instances is not subsumed by one
//! without. The told hierarchy, read from subclass, equivalence and
//! disjoint-union axioms between named classes and intersections of them,
//! settles more pairs: a class is subsumed by its told parents; it is not
//! subsumed by a class whose told parent it is known not to be subsumed by; and
//! it is subsumed by every class that one of its classified told parents is
//! subsumed by. Classes are classified roughly parents first, so most pairs
//! need no query. The pairs left open are tested in groups: one satisfiability
//! query asks whether the class has an instance outside every class of a
//! group, which, when it has, refutes the whole group at once; otherwise the
//! group is halved, and a single class the class cannot escape subsumes it.
//! Each round tests the open classes whose told parents all subsume the class,
//! so their told children are refuted without a query, and a final test takes
//! whatever is still open. `None` means that a query was not answered or a
//! list would exceed the `usize` range.
#![allow(
    clippy::ptr_arg,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::too_many_arguments,
    clippy::vec_init_then_push,
    clippy::question_mark,
    clippy::manual_map,
    clippy::collapsible_match,
    clippy::len_zero
)] // Indexed operations, explicit branches and pushes for the pinned extraction subset.

use crate::data_ontology::{prepared_class_satisfiable, Prepared};
use crate::model::{AnnotatedAxiom, AtLeastTwo, Axiom, Class, ClassExpression};
use crate::nnf::copy_iri;
use crate::symbols::same_spelling;

/// The answers: `satisfiable[i]` whether class `i` can have an instance, and
/// `subsumed[i][j]` whether every instance of class `i` is one of class `j`.
pub struct Classification {
    pub satisfiable: Vec<bool>,
    pub subsumed: Vec<Vec<bool>>,
}

fn named(class: &Class) -> ClassExpression {
    ClassExpression::Class(Class {
        iri: copy_iri(&class.iri),
    })
}

/// The index of the first class of `classes[index..]` with the class's IRI,
/// or the length of the list.
fn position(classes: &Vec<Class>, class: &Class, index: usize) -> usize {
    if index < classes.len() {
        if same_spelling(&classes[index].iri.spelling, &class.iri.spelling) {
            index
        } else {
            position(classes, class, index + 1)
        }
    } else {
        classes.len()
    }
}

/// `parents` with `parent` added to the told parents of `child`, when both are
/// listed classes.
fn tell(
    classes: &Vec<Class>,
    child: &Class,
    parent: &Class,
    mut parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    let c = position(classes, child, 0);
    let p = position(classes, parent, 0);
    if c < parents.len() && p < classes.len() {
        if parents[c].len() < usize::MAX {
            parents[c].push(p);
        }
    }
    parents
}

/// `parents` with a named `member` added as a told parent of `child`.
fn tell_named(
    classes: &Vec<Class>,
    child: &Class,
    member: &ClassExpression,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    match member {
        ClassExpression::Class(parent) => tell(classes, child, parent, parents),
        _ => parents,
    }
}

/// `parents` with every named member of `members[index..]` added as a told
/// parent of `child`.
fn tell_members(
    classes: &Vec<Class>,
    child: &Class,
    members: &Vec<ClassExpression>,
    index: usize,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    if index < members.len() {
        let parents = tell_named(classes, child, &members[index], parents);
        tell_members(classes, child, members, index + 1, parents)
    } else {
        parents
    }
}

/// `parents` with the told parents that `child ⊑ expression` gives: a named
/// class, or the named members of an intersection.
fn tell_expression(
    classes: &Vec<Class>,
    child: &Class,
    expression: &ClassExpression,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    match expression {
        ClassExpression::Class(parent) => tell(classes, child, parent, parents),
        ClassExpression::ObjectIntersectionOf(members) => {
            let parents = tell_named(classes, child, &members.first, parents);
            let parents = tell_named(classes, child, &members.second, parents);
            tell_members(classes, child, &members.rest, 0, parents)
        }
        _ => parents,
    }
}

/// `parents` with the told parents that every expression of `members[index..]`
/// gives `child`.
fn tell_list(
    classes: &Vec<Class>,
    child: &Class,
    members: &Vec<ClassExpression>,
    index: usize,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    if index < members.len() {
        let parents = tell_expression(classes, child, &members[index], parents);
        tell_list(classes, child, members, index + 1, parents)
    } else {
        parents
    }
}

/// `parents` with the told parents that all members of an equivalence give a
/// named member `child`.
fn tell_all(
    classes: &Vec<Class>,
    child: &Class,
    members: &AtLeastTwo<ClassExpression>,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    let parents = tell_expression(classes, child, &members.first, parents);
    let parents = tell_expression(classes, child, &members.second, parents);
    tell_list(classes, child, &members.rest, 0, parents)
}

/// `parents` with the told parents of `member` of an equivalence, when it is
/// named.
fn tell_member(
    classes: &Vec<Class>,
    member: &ClassExpression,
    members: &AtLeastTwo<ClassExpression>,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    match member {
        ClassExpression::Class(child) => tell_all(classes, child, members, parents),
        _ => parents,
    }
}

/// `parents` with the told parents of every named member of `rest[index..]`
/// of an equivalence.
fn tell_equivalent_rest(
    classes: &Vec<Class>,
    members: &AtLeastTwo<ClassExpression>,
    index: usize,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    if index < members.rest.len() {
        let parents = tell_member(classes, &members.rest[index], members, parents);
        tell_equivalent_rest(classes, members, index + 1, parents)
    } else {
        parents
    }
}

/// `parents` with the told parents of every named member of an equivalence.
fn tell_equivalent(
    classes: &Vec<Class>,
    members: &AtLeastTwo<ClassExpression>,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    let parents = tell_member(classes, &members.first, members, parents);
    let parents = tell_member(classes, &members.second, members, parents);
    tell_equivalent_rest(classes, members, 0, parents)
}

/// `parents` with the class of a disjoint union told to be a parent of
/// `member`, when it is named.
fn tell_under(
    classes: &Vec<Class>,
    union: &Class,
    member: &ClassExpression,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    match member {
        ClassExpression::Class(child) => tell(classes, child, union, parents),
        _ => parents,
    }
}

/// `parents` with the class of a disjoint union told to be a parent of every
/// named member of `members[index..]`.
fn tell_union_rest(
    classes: &Vec<Class>,
    union: &Class,
    members: &Vec<ClassExpression>,
    index: usize,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    if index < members.len() {
        let parents = tell_under(classes, union, &members[index], parents);
        tell_union_rest(classes, union, members, index + 1, parents)
    } else {
        parents
    }
}

/// `parents` with the class of a disjoint union told to be a parent of every
/// named member.
fn tell_union(
    classes: &Vec<Class>,
    union: &Class,
    members: &AtLeastTwo<ClassExpression>,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    let parents = tell_under(classes, union, &members.first, parents);
    let parents = tell_under(classes, union, &members.second, parents);
    tell_union_rest(classes, union, &members.rest, 0, parents)
}

/// `parents` with the told parents that one axiom gives.
fn tell_axiom(classes: &Vec<Class>, axiom: &Axiom, parents: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    match axiom {
        Axiom::SubClassOf(sub, parent) => match sub {
            ClassExpression::Class(child) => tell_expression(classes, child, parent, parents),
            _ => parents,
        },
        Axiom::EquivalentClasses(members) => tell_equivalent(classes, members, parents),
        Axiom::DisjointUnion(union, members) => tell_union(classes, union, members, parents),
        _ => parents,
    }
}

/// `parents` with the told parents that `items[index..]` give.
fn told_from(
    items: &Vec<AnnotatedAxiom>,
    classes: &Vec<Class>,
    index: usize,
    parents: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    if index < items.len() {
        let parents = tell_axiom(classes, &items[index].axiom, parents);
        told_from(items, classes, index + 1, parents)
    } else {
        parents
    }
}

/// `out` with empty rows until it has `count`.
fn empty_rows(count: usize, mut out: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    if out.len() < count {
        out.push(Vec::new());
        empty_rows(count, out)
    } else {
        out
    }
}

/// The told parents of every listed class.
pub fn told(items: &Vec<AnnotatedAxiom>, classes: &Vec<Class>) -> Vec<Vec<usize>> {
    told_from(items, classes, 0, empty_rows(classes.len(), Vec::new()))
}

/// `out` followed by the satisfiability answers for `classes[index..]`.
fn satisfiable_from(
    prepared: &Prepared,
    classes: &Vec<Class>,
    index: usize,
    mut out: Vec<bool>,
) -> Option<Vec<bool>> {
    if index < classes.len() {
        match prepared_class_satisfiable(prepared, &named(&classes[index])) {
            Some(answer) => {
                if out.len() < usize::MAX {
                    out.push(answer);
                    satisfiable_from(prepared, classes, index + 1, out)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some(out)
    }
}

/// The greatest told depth among `listed[index..]` plus one, at least `best`
/// and at most `cap`.
fn deepest(
    depth: &Vec<usize>,
    listed: &Vec<usize>,
    index: usize,
    best: usize,
    cap: usize,
) -> usize {
    if index < listed.len() {
        let parent = listed[index];
        let next = if parent < depth.len() && depth[parent] < cap && best <= depth[parent] {
            depth[parent] + 1
        } else {
            best
        };
        deepest(depth, listed, index + 1, next, cap)
    } else {
        best
    }
}

/// One round of told depths: every class from `index` on gets one more than its
/// deepest told parent.
fn deepen(
    parents: &Vec<Vec<usize>>,
    mut depth: Vec<usize>,
    cap: usize,
    index: usize,
) -> Vec<usize> {
    if index < depth.len() && index < parents.len() {
        let best = deepest(&depth, &parents[index], 0, depth[index], cap);
        depth[index] = best;
        deepen(parents, depth, cap, index + 1)
    } else {
        depth
    }
}

/// `rounds` rounds of told depths.
fn depths(parents: &Vec<Vec<usize>>, depth: Vec<usize>, cap: usize, rounds: usize) -> Vec<usize> {
    if rounds > 0 {
        let depth = deepen(parents, depth, cap, 0);
        depths(parents, depth, cap, rounds - 1)
    } else {
        depth
    }
}

/// `out` followed by the classes of `depth[index..]` at depth `level`.
fn at_level(depth: &Vec<usize>, level: usize, index: usize, mut out: Vec<usize>) -> Vec<usize> {
    if index < depth.len() {
        if depth[index] == level && out.len() < usize::MAX {
            out.push(index);
        }
        at_level(depth, level, index + 1, out)
    } else {
        out
    }
}

/// `out` followed by the classes by told depth from `level` to `cap`.
fn levels(depth: &Vec<usize>, level: usize, cap: usize, out: Vec<usize>) -> Vec<usize> {
    if level <= cap && level < usize::MAX {
        let out = at_level(depth, level, 0, out);
        levels(depth, level + 1, cap, out)
    } else {
        out
    }
}

/// `out` with `value` until it has `count` entries.
fn filled(count: usize, value: u8, mut out: Vec<u8>) -> Vec<u8> {
    if out.len() < count {
        out.push(value);
        filled(count, value, out)
    } else {
        out
    }
}

/// `out` with zeros until it has `count` entries.
fn zeros(count: usize, mut out: Vec<usize>) -> Vec<usize> {
    if out.len() < count {
        out.push(0);
        zeros(count, out)
    } else {
        out
    }
}

/// `out` with `false` until it has `count` entries.
fn unclassified(count: usize, mut out: Vec<bool>) -> Vec<bool> {
    if out.len() < count {
        out.push(false);
        unclassified(count, out)
    } else {
        out
    }
}

/// `out` with rows of `count` unknown answers until it has `count` rows.
fn unknown_rows(count: usize, mut out: Vec<Vec<u8>>) -> Vec<Vec<u8>> {
    if out.len() < count {
        out.push(filled(count, UNKNOWN, Vec::new()));
        unknown_rows(count, out)
    } else {
        out
    }
}

const UNKNOWN: u8 = 0;
const NO: u8 = 1;
const YES: u8 = 2;

/// Whether `listed[index..]` has the item.
fn listed(list: &Vec<usize>, item: usize, index: usize) -> bool {
    if index < list.len() {
        if list[index] == item {
            true
        } else {
            listed(list, item, index + 1)
        }
    } else {
        false
    }
}

/// Whether the row answers `no` for a told parent in `parents[index..]`.
fn refused(row: &Vec<u8>, parents: &Vec<usize>, index: usize) -> bool {
    if index < parents.len() {
        let parent = parents[index];
        if parent < row.len() && row[parent] == NO {
            true
        } else {
            refused(row, parents, index + 1)
        }
    } else {
        false
    }
}

/// Whether a classified told parent in `parents[index..]` is subsumed by `b`.
fn inherited(
    rows: &Vec<Vec<u8>>,
    done: &Vec<bool>,
    parents: &Vec<usize>,
    b: usize,
    index: usize,
) -> bool {
    if index < parents.len() {
        let parent = parents[index];
        if parent < done.len()
            && parent < rows.len()
            && done[parent]
            && b < rows[parent].len()
            && rows[parent][b] == YES
        {
            true
        } else {
            inherited(rows, done, parents, b, index + 1)
        }
    } else {
        false
    }
}

/// Whether class `b` is known to have no instance.
fn unsatisfiable(satisfiable: &Vec<bool>, b: usize) -> bool {
    if b < satisfiable.len() {
        !satisfiable[b]
    } else {
        false
    }
}

/// Whether `b` is a told parent of `a`.
fn told_parent(parents: &Vec<Vec<usize>>, a: usize, b: usize) -> bool {
    if a < parents.len() {
        listed(&parents[a], b, 0)
    } else {
        false
    }
}

/// Whether the row answers `no` for a told parent of `b`.
fn refuted(row: &Vec<u8>, parents: &Vec<Vec<usize>>, b: usize) -> bool {
    if b < parents.len() {
        refused(row, &parents[b], 0)
    } else {
        false
    }
}

/// Whether a classified told parent of `a` is subsumed by `b`.
fn inherits(
    rows: &Vec<Vec<u8>>,
    done: &Vec<bool>,
    parents: &Vec<Vec<usize>>,
    a: usize,
    b: usize,
) -> bool {
    if a < parents.len() {
        inherited(rows, done, &parents[a], b, 0)
    } else {
        false
    }
}

/// The answer for `a ⊑ b` that the told parents, the classes without
/// instances and the classified rows settle, for a class `a` with instances;
/// `UNKNOWN` when they do not.
fn settle(
    satisfiable: &Vec<bool>,
    parents: &Vec<Vec<usize>>,
    rows: &Vec<Vec<u8>>,
    done: &Vec<bool>,
    row: &Vec<u8>,
    a: usize,
    b: usize,
) -> u8 {
    if a == b {
        YES
    } else if unsatisfiable(satisfiable, b) {
        NO
    } else if told_parent(parents, a, b) {
        YES
    } else if refuted(row, parents, b) {
        NO
    } else if inherits(rows, done, parents, a, b) {
        YES
    } else {
        UNKNOWN
    }
}

/// Whether the row has no answer for `b` yet.
fn unknown_at(row: &Vec<u8>, b: usize) -> bool {
    if b < row.len() {
        row[b] == UNKNOWN
    } else {
        false
    }
}

/// The row of `a`, with the settled answers for `order[index..]` filled in.
fn fill(
    satisfiable: &Vec<bool>,
    parents: &Vec<Vec<usize>>,
    rows: &Vec<Vec<u8>>,
    done: &Vec<bool>,
    order: &Vec<usize>,
    a: usize,
    index: usize,
    mut row: Vec<u8>,
) -> Vec<u8> {
    if index < order.len() {
        let b = order[index];
        if unknown_at(&row, b) {
            let answer = settle(satisfiable, parents, rows, done, &row, a, b);
            row[b] = answer;
        }
        fill(satisfiable, parents, rows, done, order, a, index + 1, row)
    } else {
        row
    }
}

/// Whether the row answers `yes` for every told parent in `parents[index..]`.
fn accepted(row: &Vec<u8>, parents: &Vec<usize>, index: usize) -> bool {
    if index < parents.len() {
        let parent = parents[index];
        if parent < row.len() {
            if row[parent] == YES {
                accepted(row, parents, index + 1)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether the row leaves `b` open: every open class when `all`, else the
/// open classes whose told parents the row answers `yes` for.
fn pick(row: &Vec<u8>, parents: &Vec<Vec<usize>>, all: bool, b: usize) -> bool {
    if unknown_at(row, b) {
        if all {
            true
        } else if b < parents.len() {
            accepted(row, &parents[b], 0)
        } else {
            true
        }
    } else {
        false
    }
}

/// `out` followed by the classes from `b` on that `pick` chooses.
fn candidates(
    row: &Vec<u8>,
    parents: &Vec<Vec<usize>>,
    all: bool,
    b: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if b < row.len() {
        if pick(row, parents, all, b) {
            out.push(b);
        }
        candidates(row, parents, all, b + 1, out)
    } else {
        out
    }
}

/// `out` followed by the complements of the classes `group[index..stop]`.
fn complements(
    classes: &Vec<Class>,
    group: &Vec<usize>,
    index: usize,
    stop: usize,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < stop {
        if index < group.len() {
            let b = group[index];
            if b < classes.len() {
                out.push(ClassExpression::ObjectComplementOf(Box::new(named(
                    &classes[b],
                ))));
                complements(classes, group, index + 1, stop, out)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        Some(out)
    }
}

/// Whether some model has an instance of `a` outside every class of
/// `group[start..stop]`, by the prepared query.
fn escapes(
    prepared: &Prepared,
    classes: &Vec<Class>,
    group: &Vec<usize>,
    a: usize,
    start: usize,
    stop: usize,
) -> Option<bool> {
    if a < classes.len() {
        if start < group.len() {
            let first = group[start];
            if first < classes.len() {
                match complements(classes, group, start + 1, stop, Vec::new()) {
                    Some(rest) => prepared_class_satisfiable(
                        prepared,
                        &ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
                            first: named(&classes[a]),
                            second: ClassExpression::ObjectComplementOf(Box::new(named(
                                &classes[first],
                            ))),
                            rest,
                        })),
                    ),
                    None => None,
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// The row with `code` for every class of `group[index..stop]`.
fn mark(group: &Vec<usize>, index: usize, stop: usize, code: u8, mut row: Vec<u8>) -> Vec<u8> {
    if index < stop {
        if index < group.len() {
            let b = group[index];
            if b < row.len() {
                row[b] = code;
            }
            mark(group, index + 1, stop, code, row)
        } else {
            row
        }
    } else {
        row
    }
}

/// The row of `a` with every class of `group[start..stop]` answered: all `no`
/// when `a` has an instance outside all of them, else by halves, where a
/// single class that `a` cannot escape is `yes`.
fn split(
    prepared: &Prepared,
    classes: &Vec<Class>,
    group: &Vec<usize>,
    a: usize,
    start: usize,
    stop: usize,
    row: Vec<u8>,
) -> Option<Vec<u8>> {
    if start < stop {
        match escapes(prepared, classes, group, a, start, stop) {
            Some(true) => Some(mark(group, start, stop, NO, row)),
            Some(false) => {
                if stop - start == 1 {
                    Some(mark(group, start, stop, YES, row))
                } else {
                    let middle = start + (stop - start) / 2;
                    match split(prepared, classes, group, a, start, middle, row) {
                        Some(row) => split(prepared, classes, group, a, middle, stop, row),
                        None => None,
                    }
                }
            }
            None => None,
        }
    } else {
        Some(row)
    }
}

/// The row of `a` after at most `count` rounds that settle what the row and
/// the classified rows decide and then test the open classes whose told
/// parents are all above `a`.
fn rounds(
    prepared: &Prepared,
    classes: &Vec<Class>,
    satisfiable: &Vec<bool>,
    parents: &Vec<Vec<usize>>,
    rows: &Vec<Vec<u8>>,
    done: &Vec<bool>,
    order: &Vec<usize>,
    a: usize,
    count: usize,
    row: Vec<u8>,
) -> Option<Vec<u8>> {
    if count > 0 {
        let settled = fill(satisfiable, parents, rows, done, order, a, 0, row);
        let group = candidates(&settled, parents, false, 0, Vec::new());
        if group.len() > 0 {
            match split(prepared, classes, &group, a, 0, group.len(), settled) {
                Some(tested) => rounds(
                    prepared,
                    classes,
                    satisfiable,
                    parents,
                    rows,
                    done,
                    order,
                    a,
                    count - 1,
                    tested,
                ),
                None => None,
            }
        } else {
            Some(settled)
        }
    } else {
        Some(row)
    }
}

/// The row of `a`: every answer `yes` for a class without instances, else the
/// answers of the rounds and a final test of every class still open.
fn row_of(
    prepared: &Prepared,
    classes: &Vec<Class>,
    satisfiable: &Vec<bool>,
    parents: &Vec<Vec<usize>>,
    rows: &Vec<Vec<u8>>,
    done: &Vec<bool>,
    order: &Vec<usize>,
    a: usize,
) -> Option<Vec<u8>> {
    if a < satisfiable.len() && satisfiable[a] {
        match rounds(
            prepared,
            classes,
            satisfiable,
            parents,
            rows,
            done,
            order,
            a,
            classes.len(),
            filled(classes.len(), UNKNOWN, Vec::new()),
        ) {
            Some(row) => {
                let settled = fill(satisfiable, parents, rows, done, order, a, 0, row);
                let group = candidates(&settled, parents, true, 0, Vec::new());
                split(prepared, classes, &group, a, 0, group.len(), settled)
            }
            None => None,
        }
    } else {
        Some(filled(classes.len(), YES, Vec::new()))
    }
}

/// The rows, with every class of `order[index..]` classified and then every
/// other class.
fn classify_from(
    prepared: &Prepared,
    classes: &Vec<Class>,
    satisfiable: &Vec<bool>,
    parents: &Vec<Vec<usize>>,
    order: &Vec<usize>,
    index: usize,
    mut rows: Vec<Vec<u8>>,
    mut done: Vec<bool>,
) -> Option<Vec<Vec<u8>>> {
    if index < order.len() {
        let a = order[index];
        if a < rows.len() && a < done.len() && !done[a] {
            match row_of(
                prepared,
                classes,
                satisfiable,
                parents,
                &rows,
                &done,
                order,
                a,
            ) {
                Some(row) => {
                    rows[a] = row;
                    done[a] = true;
                    classify_from(
                        prepared,
                        classes,
                        satisfiable,
                        parents,
                        order,
                        index + 1,
                        rows,
                        done,
                    )
                }
                None => None,
            }
        } else {
            classify_from(
                prepared,
                classes,
                satisfiable,
                parents,
                order,
                index + 1,
                rows,
                done,
            )
        }
    } else {
        classify_rest(
            prepared,
            classes,
            satisfiable,
            parents,
            order,
            0,
            rows,
            done,
        )
    }
}

/// The rows, with every class from `a` on classified.
fn classify_rest(
    prepared: &Prepared,
    classes: &Vec<Class>,
    satisfiable: &Vec<bool>,
    parents: &Vec<Vec<usize>>,
    order: &Vec<usize>,
    a: usize,
    mut rows: Vec<Vec<u8>>,
    mut done: Vec<bool>,
) -> Option<Vec<Vec<u8>>> {
    if a < rows.len() && a < done.len() {
        if !done[a] {
            match row_of(
                prepared,
                classes,
                satisfiable,
                parents,
                &rows,
                &done,
                order,
                a,
            ) {
                Some(row) => {
                    rows[a] = row;
                    done[a] = true;
                    classify_rest(
                        prepared,
                        classes,
                        satisfiable,
                        parents,
                        order,
                        a + 1,
                        rows,
                        done,
                    )
                }
                None => None,
            }
        } else {
            classify_rest(
                prepared,
                classes,
                satisfiable,
                parents,
                order,
                a + 1,
                rows,
                done,
            )
        }
    } else {
        Some(rows)
    }
}

/// `out` followed by the answers of `row[index..]` as Booleans.
fn answers(row: &Vec<u8>, index: usize, mut out: Vec<bool>) -> Vec<bool> {
    if index < row.len() {
        if out.len() < usize::MAX {
            out.push(row[index] == YES);
        }
        answers(row, index + 1, out)
    } else {
        out
    }
}

/// `out` followed by the rows of `rows[index..]` as Booleans.
fn all_answers(rows: &Vec<Vec<u8>>, index: usize, mut out: Vec<Vec<bool>>) -> Vec<Vec<bool>> {
    if index < rows.len() {
        if out.len() < usize::MAX {
            out.push(answers(&rows[index], 0, Vec::new()));
        }
        all_answers(rows, index + 1, out)
    } else {
        out
    }
}

/// Classify the listed classes of a prepared closure of `items`.
pub fn classify(
    prepared: &Prepared,
    items: &Vec<AnnotatedAxiom>,
    classes: &Vec<Class>,
) -> Option<Classification> {
    let satisfiable = match satisfiable_from(prepared, classes, 0, Vec::new()) {
        Some(answers) => answers,
        None => return None,
    };
    let parents = told(items, classes);
    let depth = depths(&parents, zeros(classes.len(), Vec::new()), 32, 32);
    let order = levels(&depth, 0, 32, Vec::new());
    let rows = unknown_rows(classes.len(), Vec::new());
    let done = unclassified(classes.len(), Vec::new());
    match classify_from(
        prepared,
        classes,
        &satisfiable,
        &parents,
        &order,
        0,
        rows,
        done,
    ) {
        Some(rows) => Some(Classification {
            satisfiable,
            subsumed: all_answers(&rows, 0, Vec::new()),
        }),
        None => None,
    }
}
