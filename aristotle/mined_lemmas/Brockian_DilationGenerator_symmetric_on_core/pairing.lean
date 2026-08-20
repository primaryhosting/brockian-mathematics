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

noncomputable def pairing (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * (f x * starRingEnd ℂ (g x))

/-- Conjugation `ℂ → ℂ` is smooth as a map of real normed spaces. -/
