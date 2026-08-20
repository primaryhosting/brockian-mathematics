import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace DilationGenerator

/-- The pointwise product `x ↦ x · f x · conj (g x)`, whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/

theorem hasCompactSupport_pairing {f g : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (pairing f g) := by
  have h1 : HasCompactSupport (fun x : ℝ => f x * starRingEnd ℂ (g x)) :=
    hfc.mul_right
  exact h1.mul_left

/-- The integral over `(0, ∞)` of the derivative of `pairing f g` vanishes: the boundary
term at `0` is killed by the factor `x`, and the one at `+∞` by compact support. -/
