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

theorem sat_transImp (hd : ∀ t, t < T → StepData M c t (tr t)) :
    ∀ cl ∈ transImp M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [transImp, List.mem_flatMap, List.mem_range, List.mem_append] at hcl
  obtain ⟨t, ht, τ, hτ, hcl⟩ := hcl
  by_cases hA : assignOf c tr (vTr t τ) = true
  · have heq : tr t = τ := (assignOf_vTr_iff t τ).mp hA
    obtain ⟨e1, e2, -, e4, e5, e6⟩ := hd t ht
    rw [heq] at e1 e2 e4 e5 e6
    rcases hcl with hcl | hcl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · rw [clause_eval_iff]
        exact ⟨lp (vS t τ.1), by simp, by simp [lp, e1]⟩
      · rw [clause_eval_iff]
        exact ⟨lp (vS (t + 1) τ.2.2.1), by simp, by simp [lp, e4]⟩
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hcl
      obtain ⟨i, -, hcl⟩ := hcl
      by_cases hh : (c t).head = i
      · subst hh
        rcases hcl with rfl | rfl | rfl
        · rw [clause_eval_iff]
          exact ⟨lp (vC t (c t).head τ.2.1), by simp, by simp [lp, e2]⟩
        · rw [clause_eval_iff]
          refine ⟨lp (vC (t + 1) (c t).head τ.2.2.2.1), by simp, ?_⟩
          simp only [lp, assignOf_vC, decide_eq_true_eq, e5, writeTape, if_pos]
        · rw [clause_eval_iff]
          refine ⟨lp (vH (t + 1) (τ.2.2.2.2.apply (c t).head)), by simp, ?_⟩
          simp [lp, e6]
      · rcases hcl with rfl | rfl | rfl <;> rw [clause_eval_iff] <;>
          exact ⟨ln (vH t i), by simp, by simp [ln, hh]⟩
  · have hA' : assignOf c tr (vTr t τ) = false := by
      cases hv : assignOf c tr (vTr t τ) with
      | false => rfl
      | true => exact absurd hv hA
    rcases hcl with hcl | hcl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> rw [clause_eval_iff] <;>
        exact ⟨ln (vTr t τ), by simp, by simp [ln, hA']⟩
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hcl
      obtain ⟨i, -, hcl⟩ := hcl
      rcases hcl with rfl | rfl | rfl <;> rw [clause_eval_iff] <;>
        exact ⟨ln (vTr t τ), by simp, by simp [ln, hA']⟩

