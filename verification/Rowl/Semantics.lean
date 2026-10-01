import Rowl.Generated.RowlKernel

namespace Rowl
open RowlRust.prototype

/-- Independent declarative membership semantics for the prototype language.
    A valuation specifies whether a single element belongs to each atomic class. -/
def denotes : Formula → Valuation → Prop
  | .Top, _ => True
  | .Bottom, _ => False
  | .Atom .A, v => v.a = true
  | .Atom .B, v => v.b = true
  | .Not f, v => ¬ denotes f v
  | .And left right, v => denotes left v ∧ denotes right v
  | .Or left right, v => denotes left v ∨ denotes right v

/-- There exists an element with membership satisfying the expression. -/
def satisfiable (f : Formula) : Prop := ∃ v, denotes f v

/-- Declarative meaning of each answer; no operational search appears here. -/
def correctDecision (f : Formula) : Decision → Prop
  | .Satisfiable v => denotes f v
  | .Unsatisfiable => ¬ satisfiable f

end Rowl
