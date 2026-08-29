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

theorem sat_cellAtMostOne : ∀ cl ∈ cellAtMostOne T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [cellAtMostOne, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨t, -, i, -, s, -, s', -, hcl⟩ := hcl
  by_cases hss : s = s'
  · simp [hss] at hcl
  · simp only [hss, if_false, List.mem_cons, List.not_mem_nil, or_false] at hcl
    subst hcl
    rw [clause_eval_iff]
    by_cases hc : (c t).tape i = s
    · refine ⟨ln (vC t i s'), by simp, ?_⟩
      simp only [ln, assignOf_vC, decide_eq_false_iff_not]
      intro hcon
      exact hss (hc ▸ symCode_inj hcon)
    · refine ⟨ln (vC t i s), by simp, ?_⟩
      simp only [ln, assignOf_vC, decide_eq_false_iff_not]
      intro hcon
      exact hc (symCode_inj hcon)

