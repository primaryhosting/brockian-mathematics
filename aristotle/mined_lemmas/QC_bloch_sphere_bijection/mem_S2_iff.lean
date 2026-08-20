import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

set_option grind.warning false

namespace QC

open Complex

/-- A normalized qubit state vector: a unit vector in `ℂ²`. -/

lemma mem_S2_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ S2 ↔ x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 = 1 := by
  rw [S2, mem_sphere_iff_norm, sub_zero, EuclideanSpace.norm_eq]
  constructor
  · intro h
    have h2 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ ∑ i, ‖x.ofLp i‖ ^ 2)
    rw [h] at h2
    simpa [Fin.sum_univ_three, sq_abs] using h2.symm
  · intro h
    rw [show (∑ i, ‖x.ofLp i‖ ^ 2) = 1 by simpa [Fin.sum_univ_three, sq_abs] using h]
    simp

/-- The Bloch vector of a state vector `(a, b) ∈ ℂ²`. -/
