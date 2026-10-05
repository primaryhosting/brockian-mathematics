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

theorem assignOf_vTr_iff (t : Nat) (τ : Trans) :
    assignOf c tr (vTr t τ) = true ↔ tr t = τ := by
  obtain ⟨q, a, q', b, d⟩ := τ
  have hval : assignOf c tr (vTr t (q, a, q', b, d)) =
      decide ((tr t).1 = q ∧ symCode (tr t).2.1 = symCode a ∧ (tr t).2.2.1 = q' ∧
        symCode (tr t).2.2.2.1 = symCode b ∧ moveCode (tr t).2.2.2.2 = moveCode d) := rfl
  rw [hval]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨q0, a0, q0', b0, d0⟩ := tr t
    simp only at h1 h2 h3 h4 h5
    rw [h1, symCode_inj h2, h3, symCode_inj h4, moveCode_inj h5]
  · intro h
    rw [h]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

