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

theorem pick_eq_tabRow {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (A : TVar n → Bool)
    (hcell : CNF.eval A (cellClauses n T (tabWidth T x m)) = true)
    (hinit : CNF.eval A (initClauses M T x m) = true)
    (htrans : CNF.eval A (transClauses M T (tabWidth T x m)) = true) :
    ∀ t, t ≤ T → ∀ i, i < tabWidth T x m →
      pick A t i = tabRow M (x ++ pickWitness A x m) t i := by
  intro t
  induction t with
  | zero => intro _; exact pick_eq_tabRow_zero M T x m A hcell hinit
  | succ t ih =>
    intro ht
    exact pick_eq_tabRow_step M T x m A hcell htrans t ht (ih (by omega))

