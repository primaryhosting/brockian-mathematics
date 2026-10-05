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

theorem frame_step {t j : Nat} {s : Sym} (ht : t < T) (hj : j ≤ T)
    (h1 : A (vH t j) = false) (h2 : A (vC t j s) = true) : A (vC (t + 1) j s) = true := by
  have hc : [lp (vH t j), ln (vC t j s), lp (vC (t + 1) j s)] ∈ frameClauses T := by
    simp only [frameClauses, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨t, ht, j, by omega, s, mem_syms s, rfl⟩
  have h := hsat _ (mem_tab_frameClauses hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [lp, h1] at hv
  · simp [ln, h2] at hv
  · simpa [lp] using hv

/-! ## Extracting a computation from a satisfying assignment -/

omit hsat in
