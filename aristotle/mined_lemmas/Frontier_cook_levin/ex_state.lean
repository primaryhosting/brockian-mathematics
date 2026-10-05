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

theorem ex_state {t : Nat} (ht : t ≤ T) : ∃ q, q < M.numStates ∧ A (vS t q) = true := by
  have hc : ((List.range M.numStates).map fun q => lp (vS t q)) ∈ stateOne M T := by
    simp only [stateOne, List.mem_map, List.mem_range]
    exact ⟨t, by omega, rfl⟩
  have h := hsat _ (mem_tab_stateOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨q, hq, rfl⟩ := hl
  exact ⟨q, hq, by simpa [lp] using hv⟩

