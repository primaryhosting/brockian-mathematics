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

theorem sat_initClauses (hrun : M.Run x T c) :
    ∀ cl ∈ initClauses M T x, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  have h0 : c 0 = M.init x := hrun.1
  simp only [initClauses, List.mem_cons, List.mem_map, List.mem_range] at hcl
  rcases hcl with rfl | rfl | ⟨i, -, rfl⟩
  · rw [clause_eval_iff]
    exact ⟨lp (vS 0 M.start), by simp, by simp [lp, h0, NTM.init]⟩
  · rw [clause_eval_iff]
    exact ⟨lp (vH 0 0), by simp, by simp [lp, h0, NTM.init]⟩
  · rw [clause_eval_iff]
    exact ⟨lp (vC 0 i (inputTape x i)), by simp, by simp [lp, h0, NTM.init]⟩

