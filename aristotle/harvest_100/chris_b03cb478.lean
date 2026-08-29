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
def original (c : Ctx) : Prop :=
  match c.cap with
  | Capability.read  => True
  | Capability.write => c.trusted = true
  | Capability.net   => c.sameOrigin = true ∧ 0 < c.budget

/-- The tightened admission predicate: every branch is strengthened. -/
def tightened (c : Ctx) : Prop :=
  match c.cap with
  | Capability.read  => c.trusted = true ∨ c.sameOrigin = true
  | Capability.write => c.trusted = true ∧ 0 < c.budget
  | Capability.net   => c.sameOrigin = true ∧ c.trusted = true ∧ 1 ≤ c.budget

/-- **Refinement.** Anything admitted by the tightened isolation predicate is
also admitted by the original one: the tightening only ever removes behaviours,
so the engine's model stays sound with respect to the original specification. -/
theorem tightened_predicate_refines_original (c : Ctx) :
    tightened c → original c := by
  cases hcap : c.cap with
  | read =>
      intro _
      simp [original, hcap]
  | write =>
      intro h
      simp only [tightened, hcap] at h
      simpa [original, hcap] using h.1
  | net =>
      intro h
      simp only [tightened, hcap] at h
      simp only [original, hcap]
      exact ⟨h.1, h.2.2⟩

/-- The refinement is strict: the tightened predicate rejects some contexts that
the original predicate admits. -/
theorem tightened_strictly_refines_original :
    ∃ c : Ctx, original c ∧ ¬ tightened c := by
  refine ⟨⟨Capability.read, false, false, 0⟩, ?_, ?_⟩
  · trivial
  · simp [tightened]

end Isolation
end PCA

