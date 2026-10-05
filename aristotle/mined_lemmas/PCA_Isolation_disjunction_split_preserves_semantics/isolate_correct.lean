/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-! ## Policies

The isolation engine of a proof-carrying application reasons about *isolation
policies*: propositional constraints over atomic capabilities (permissions,
resource handles, ...).  A *state* of the machine is an assignment of a Boolean
truth value to every capability. -/

/-- Atomic capabilities are indexed by natural numbers. -/
abbrev Cap := Nat

/-- A machine state: which capabilities are currently granted. -/
abbrev State := Cap → Bool

/-- Isolation policies. -/
inductive Policy where
  | tt : Policy
  | ff : Policy
  | atom : Cap → Policy
  | neg : Policy → Policy
  | and : Policy → Policy → Policy
  | or : Policy → Policy → Policy
  deriving DecidableEq, Repr

namespace Policy

/-- Boolean semantics of a policy in a state. -/

theorem isolate_correct (p : Policy) :
    isolate p ≠ [] ∧
    (∀ b ∈ isolate p, IsCube b = true) ∧
    (∀ s : State, eval s p = true ↔ ∃ b ∈ isolate p, eval s b = true) := by
  refine ⟨split_ne_nil _, split_isCube_of_isNNF _ (isNNF_nnf p), fun s => ?_⟩
  rw [← eval_nnf s p]
  exact disjunction_split_preserves_semantics s (nnf p)

/-! ## Sanity checks -/

section Examples

/-- `(c₀ ∨ c₁) ∧ c₂` splits into the two isolated branches `c₀ ∧ c₂` and
`c₁ ∧ c₂`. -/
example :
    split (Policy.and (Policy.or (Policy.atom 0) (Policy.atom 1)) (Policy.atom 2)) =
      [Policy.and (Policy.atom 0) (Policy.atom 2),
       Policy.and (Policy.atom 1) (Policy.atom 2)] := by
  decide

/-- Negation normal form pushes negations down to the capabilities. -/
example :
    nnf (Policy.neg (Policy.and (Policy.atom 0) (Policy.atom 1))) =
      Policy.or (Policy.neg (Policy.atom 0)) (Policy.neg (Policy.atom 1)) := by
  decide

end Examples

end PCA.Isolation

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

