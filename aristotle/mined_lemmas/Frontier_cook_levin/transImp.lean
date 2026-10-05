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

def transImp : CNF Var :=
  (List.range T).flatMap fun t =>
    (transList M).flatMap fun τ =>
      [[ln (vTr t τ), lp (vS t τ.1)], [ln (vTr t τ), lp (vS (t + 1) τ.2.2.1)]] ++
        (List.range (T + 1)).flatMap fun i =>
          [[ln (vTr t τ), ln (vH t i), lp (vC t i τ.2.1)],
            [ln (vTr t τ), ln (vH t i), lp (vC (t + 1) i τ.2.2.2.1)],
            [ln (vTr t τ), ln (vH t i), lp (vH (t + 1) (τ.2.2.2.2.apply i))]]

/-- Cells away from the head do not change. -/
