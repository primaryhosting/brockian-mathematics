/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no `import`, so that the module
docstring above can literally be the first thing in the file).  The definitions of `Lit`,
`Clause`, `CNF`, `Clause.eval` and `CNF.eval` below mirror `Std.Sat.Literal`,
`Std.Sat.CNF.Clause`, `Std.Sat.CNF`, `Std.Sat.CNF.Clause.eval` and `Std.Sat.CNF.eval`
from the Lean standard library.
-/

namespace Frontier

/-! ## Propositional formulas in conjunctive normal form -/

/-- A literal: a variable together with the sign with which it occurs. -/
abbrev Lit (V : Type) := V × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type) := List (Lit V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (V : Type) := List (Clause V)

/-- Value of a clause under an assignment. -/

def ln {V : Type} (v : V) : Lit V := (v, false)

/-! ## Nondeterministic Turing machines -/

/-- Tape symbols: `none` is the blank symbol. -/
abbrev Sym := Option Bool

/-- Head movements. -/
inductive Move where
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- Effect of a head movement on a position (the tape is one-way infinite, so moving
left at position `0` stays at `0`). -/
