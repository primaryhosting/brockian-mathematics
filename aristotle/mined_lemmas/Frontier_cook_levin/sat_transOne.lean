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

theorem sat_transOne (hrun : M.Run x T c) (hd : ∀ t, t < T → StepData M c t (tr t)) :
    ∀ cl ∈ transOne M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [transOne, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, rfl⟩ := hcl
  obtain ⟨e1, e2, e3, -, -, -⟩ := hd t ht
  rw [clause_eval_iff]
  refine ⟨lp (vTr t (tr t)), ?_, ?_⟩
  · simp only [List.mem_map]
    refine ⟨tr t, mem_transList.mpr ⟨?_, e3⟩, rfl⟩
    rw [e1]
    exact run_state_lt hrun t (by omega)
  · simp only [lp]
    exact (assignOf_vTr_iff t (tr t)).mpr rfl

