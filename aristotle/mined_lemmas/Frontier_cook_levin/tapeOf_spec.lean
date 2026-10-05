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

theorem tapeOf_spec {t j : Nat} (ht : t ≤ T) (hj : j ≤ T) :
    A (vC t j (tapeOf A T x t j)) = true := by
  obtain ⟨s, hs⟩ := ex_cell hsat ht hj
  unfold tapeOf
  rw [if_pos hj]
  by_cases h0 : A (vC t j none) = true
  · simp [h0]
  · by_cases h1 : A (vC t j (some false)) = true
    · simp [h0, h1]
    · simp only [h0, h1, if_false, Bool.false_eq_true]
      cases s with
      | none => exact absurd hs h0
      | some bb =>
        cases bb with
        | false => exact absurd hs h1
        | true => exact hs

omit hsat in
