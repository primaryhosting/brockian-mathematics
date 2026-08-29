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

theorem satisfiable_tableau_iff {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat) :
    Satisfiable (tableau M T x m) ↔ ∃ w : List Bool, w.length = m ∧ M.Accepts T (x ++ w) := by
  constructor
  · exact accepts_of_satisfiable_tableau M T x m
  · rintro ⟨w, hw, hacc⟩
    exact satisfiable_tableau_of_accepts M T x m w hw hacc

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

