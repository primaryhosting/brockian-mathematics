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

theorem sat_headOne (hrun : M.Run x T c) :
    ∀ cl ∈ headOne T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [headOne, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, rfl⟩ := hcl
  rw [clause_eval_iff]
  refine ⟨lp (vH t (c t).head), ?_, ?_⟩
  · simp only [List.mem_map, List.mem_range]
    exact ⟨(c t).head, by have := run_head_le hrun t (by omega); omega, rfl⟩
  · simp [lp]

