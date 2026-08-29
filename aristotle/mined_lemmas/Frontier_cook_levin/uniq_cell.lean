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

theorem uniq_cell {t i : Nat} {s s' : Sym} (ht : t ≤ T) (hi : i ≤ T)
    (h1 : A (vC t i s) = true) (h2 : A (vC t i s') = true) : s = s' := by
  by_cases hne : s = s'
  · exact hne
  exfalso
  have hc : [ln (vC t i s), ln (vC t i s')] ∈ cellAtMostOne T := by
    simp only [cellAtMostOne, List.mem_flatMap, List.mem_range]
    exact ⟨t, by omega, i, by omega, s, mem_syms s, s', mem_syms s', by simp [hne]⟩
  have h := hsat _ (mem_tab_cellAtMostOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv

