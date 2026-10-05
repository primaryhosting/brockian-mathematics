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

/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

/-- The capabilities an isolated component may request from the host. -/
inductive Capability
  | read
  | write
  | net
  deriving DecidableEq, Repr

/-- The security-relevant part of an isolation context: which capability is being
exercised, whether the request is same-origin, whether the principal is trusted,
and how much of the resource budget is left. -/
structure Ctx where
  cap : Capability
  sameOrigin : Bool
  trusted : Bool
  budget : Nat
  deriving Repr

/-- The original admission predicate of the isolation engine. -/

theorem tightened_strictly_refines_original :
    ∃ c : Ctx, original c ∧ ¬ tightened c := by
  refine ⟨⟨Capability.read, false, false, 0⟩, ?_, ?_⟩
  · trivial
  · simp [tightened]

end Isolation
end PCA

