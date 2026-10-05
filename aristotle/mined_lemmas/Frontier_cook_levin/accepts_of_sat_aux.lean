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

theorem accepts_of_sat_aux : M.AcceptsWithin x T := by
  refine ⟨cfgOf M A T x, ⟨cfgOf_zero hsat, fun t ht => step_of_sat hsat ht⟩, ?_⟩
  obtain ⟨t, ht, hacc⟩ := ex_accept hsat
  refine ⟨t, ht, ?_⟩
  have hs := stateOf_spec hsat ht
  simp only [cfgOf_state]
  exact uniq_state hsat ht hs.1 M.accept_lt hs.2 hacc

end Extract

