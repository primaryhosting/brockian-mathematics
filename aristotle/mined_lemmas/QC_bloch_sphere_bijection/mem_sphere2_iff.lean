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

/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`, recorded as a pair of amplitudes
`(a, b)` with `|a|² + |b|² = 1`. -/

theorem mem_sphere2_iff (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ Sphere2 ↔ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  rw [mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  constructor
  · intro h
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2), h]
  · intro h; rw [h]; simp

/-- The Bloch vector of a pure state `(a, b)`:
`(2 Re(conj a · b), 2 Im(conj a · b), |a|² - |b|²)`. -/
