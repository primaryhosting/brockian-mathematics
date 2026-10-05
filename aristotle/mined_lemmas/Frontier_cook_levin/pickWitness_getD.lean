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

theorem pickWitness_getD {n : Nat} (A : TVar n → Bool) (x : List Bool) (m j : Nat)
    (hj : j < m) :
    (pickWitness A x m).getD j false = ((pick A 0 (x.length + 1 + j)).1).getD false := by
  have hj' : j < (pickWitness A x m).length := by rw [pickWitness_length]; exact hj
  rw [List.getD, List.getElem?_eq_getElem hj']
  simp [pickWitness]

