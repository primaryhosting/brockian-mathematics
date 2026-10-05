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

theorem cfgOf_zero : cfgOf M A T x 0 = M.init x := by
  have h0 : (0 : Nat) ≤ T := Nat.zero_le _
  have hs := stateOf_spec hsat h0
  have hh := headOf_spec hsat h0
  have e1 : stateOf A M.numStates 0 = M.start :=
    uniq_state hsat h0 hs.1 M.start_lt hs.2 (init_state hsat)
  have e2 : headOf A T 0 = 0 :=
    uniq_head hsat h0 hh.1 h0 hh.2 (init_head hsat)
  have e3 : tapeOf A T x 0 = inputTape x := by
    funext j
    by_cases hj : j ≤ T
    · exact uniq_cell hsat h0 hj (tapeOf_spec hsat h0 hj) (init_cell hsat hj)
    · exact tapeOf_out hj
  simp [cfgOf, NTM.init, e1, e2, e3]

