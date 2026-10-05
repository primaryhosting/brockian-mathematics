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

theorem imp_read {t i : Nat} {τ : Trans} (ht : t < T) (hτ : τ ∈ transList M) (hi : i ≤ T)
    (h1 : A (vTr t τ) = true) (h2 : A (vH t i) = true) : A (vC t i τ.2.1) = true := by
  have hc : [ln (vTr t τ), ln (vH t i), lp (vC t i τ.2.1)] ∈ transImp M T := by
    simp only [transImp, List.mem_flatMap, List.mem_range]
    refine ⟨t, ht, τ, hτ, List.mem_append_right _ ?_⟩
    simp only [List.mem_flatMap, List.mem_range]
    exact ⟨i, by omega, by simp⟩
  have h := hsat _ (mem_tab_transImp hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv
  · simpa [lp] using hv

