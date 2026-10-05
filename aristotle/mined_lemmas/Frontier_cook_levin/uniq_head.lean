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

theorem uniq_head {t i j : Nat} (ht : t ≤ T) (hi : i ≤ T) (hj : j ≤ T)
    (h1 : A (vH t i) = true) (h2 : A (vH t j) = true) : i = j := by
  by_cases hne : i = j
  · exact hne
  exfalso
  have hc : [ln (vH t i), ln (vH t j)] ∈ headAtMostOne T := by
    simp only [headAtMostOne, List.mem_flatMap, List.mem_range]
    exact ⟨t, by omega, i, by omega, j, by omega, by simp [hne]⟩
  have h := hsat _ (mem_tab_headAtMostOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv

