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

theorem sat_frameClauses (hd : ∀ t, t < T → StepData M c t (tr t)) :
    ∀ cl ∈ frameClauses T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [frameClauses, List.mem_flatMap, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, j, -, s, -, rfl⟩ := hcl
  rw [clause_eval_iff]
  by_cases hh : (c t).head = j
  · exact ⟨lp (vH t j), by simp, by simp [lp, hh]⟩
  · by_cases hs : (c t).tape j = s
    · obtain ⟨-, -, -, -, e5, -⟩ := hd t ht
      refine ⟨lp (vC (t + 1) j s), by simp, ?_⟩
      simp only [lp, assignOf_vC, decide_eq_true_eq, e5, writeTape, if_neg (fun h => hh h.symm)]
      rw [hs]
    · refine ⟨ln (vC t j s), by simp, ?_⟩
      simp only [ln, assignOf_vC, decide_eq_false_iff_not]
      intro hcon
      exact hs (symCode_inj hcon)

end Complete

