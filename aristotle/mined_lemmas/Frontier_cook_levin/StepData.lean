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

def StepData (M : NTM) (c : Nat → Cfg) (t : Nat) (τ : Trans) : Prop :=
  τ.1 = (c t).state ∧ τ.2.1 = (c t).tape (c t).head ∧
    (τ.2.2.1, τ.2.2.2.1, τ.2.2.2.2) ∈ M.step τ.1 τ.2.1 ∧
    (c (t + 1)).state = τ.2.2.1 ∧
    (c (t + 1)).tape = writeTape (c t).tape (c t).head τ.2.2.2.1 ∧
    (c (t + 1)).head = τ.2.2.2.2.apply (c t).head

/-- The assignment describing the computation `c` with transitions `tr`. -/
