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

set_option grind.warning false

namespace QC

open Complex

/-- A pure state of a single qubit: a unit vector in `ℂ²`. -/
abbrev PureQubit : Type := Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1

/-- The 2-sphere `S²`, the unit sphere of `ℝ³`. -/
abbrev S2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1


lemma blochVec_smul (z : ℂ) (hz : ‖z‖ = 1) (v : EuclideanSpace ℂ (Fin 2)) :
    blochVec (z • v) = blochVec v := by
  have hz' : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have h0 : (z • v) 0 = z * v 0 := rfl
  have h1 : (z • v) 1 = z * v 1 := rfl
  have key : (starRingEnd ℂ) ((z • v) 0) * (z • v) 1 = (starRingEnd ℂ) (v 0) * v 1 := by
    rw [h0, h1, map_mul]
    have : (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) (v 0) * (z * v 1)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) (v 0) * v 1) := by ring
      _ = (starRingEnd ℂ) (v 0) * v 1 := by rw [this, hz']; simp
  unfold blochVec
  rw [key, h0, h1, Complex.normSq_mul, Complex.normSq_mul, hz']
  ring_nf

/-- The Bloch map from pure states modulo phase to the 2-sphere. -/
