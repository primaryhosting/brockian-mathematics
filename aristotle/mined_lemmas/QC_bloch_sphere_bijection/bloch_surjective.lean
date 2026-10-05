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

import Mathlib
/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- A pure state of a qubit: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are equivalent when they differ by a global phase. -/

lemma bloch_surjective : Function.Surjective bloch := by
  rintro ⟨p, hp⟩
  have hnorm : ‖p‖ = 1 := by simpa using hp
  have hsum : (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.sqrt_eq_one] at hnorm
    simpa [Real.norm_eq_abs, sq_abs] using hnorm
  obtain ⟨v, hv⟩ := exists_qubit_blochVec (p 0) (p 1) (p 2) hsum
  refine ⟨Quotient.mk _ v, Subtype.ext ?_⟩
  show blochVec v = p
  rw [hv]
  ext i
  fin_cases i <;> simp

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection
with the points of the two-sphere `S² ⊆ ℝ³`. -/
