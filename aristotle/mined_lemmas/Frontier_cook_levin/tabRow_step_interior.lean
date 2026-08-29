/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Frontier

/-! ## Propositional formulas in conjunctive normal form -/

/-- A literal over a type `V` of variables: a variable together with a polarity. -/
structure Lit (V : Type) where
  var : V
  pol : Bool
deriving DecidableEq

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type) := List (Lit V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (V : Type) := List (Clause V)

/-- Value of a literal under an assignment. -/

theorem tabRow_step_interior {n : Nat} (M : TM n) (u : List Bool) (t i : Nat) :
    tabRow M u (t + 1) (i + 1) =
      M.rule (tabRow M u t i) (tabRow M u t (i + 1)) (tabRow M u t (i + 2)) :=
  M.cell_step_interior _ i

