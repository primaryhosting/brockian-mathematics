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

theorem ex_cell {t i : Nat} (ht : t ≤ T) (hi : i ≤ T) : ∃ s, A (vC t i s) = true := by
  have hc : (syms.map fun s => lp (vC t i s)) ∈ cellOne T := by
    simp only [cellOne, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨t, by omega, i, by omega, rfl⟩
  have h := hsat _ (mem_tab_cellOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_map] at hl
  obtain ⟨s, _, rfl⟩ := hl
  exact ⟨s, by simpa [lp] using hv⟩

