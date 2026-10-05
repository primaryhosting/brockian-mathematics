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

def cfgOf (M : NTM) (A : Var → Bool) (T : Nat) (x : List Bool) (t : Nat) : Cfg :=
  ⟨stateOf A M.numStates t, tapeOf A T x t, headOf A T t⟩

/-! ## Reading facts off a satisfying assignment -/

section Extract

variable {M : NTM} {T : Nat} {x : List Bool} {A : Var → Bool}
  (hsat : ∀ c ∈ tableau M T x, Clause.eval A c = true)

include hsat

