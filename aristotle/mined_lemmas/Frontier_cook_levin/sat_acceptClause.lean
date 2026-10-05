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

theorem sat_acceptClause {t0 : Nat} (ht0 : t0 ≤ T) (hacc : (c t0).state = M.accept) :
    ∀ cl ∈ acceptClause M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [acceptClause, List.mem_cons, List.not_mem_nil, or_false] at hcl
  subst hcl
  rw [clause_eval_iff]
  refine ⟨lp (vS t0 M.accept), ?_, ?_⟩
  · simp only [List.mem_map, List.mem_range]
    exact ⟨t0, by omega, rfl⟩
  · simp [lp, hacc]

