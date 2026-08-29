import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Frontier

/-- The four dimensional real Hilbert space in which we work. -/
abbrev KSSpace : Type := EuclideanSpace ℝ (Fin 4)

/-- A vector of `KSSpace` given by its four coordinates. -/

lemma ksVec_inner (a b c d a' b' c' d' : ℝ) :
    ⟪ksVec a b c d, ksVec a' b' c' d'⟫_ℝ = a * a' + b * b' + c * c' + d * d' := by
  simp [ksVec, PiLp.inner_apply, Fin.sum_univ_four]
  ring

