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

/-- A pure qubit state: a unit vector in `ℂ²`. -/

theorem blochRaw_respects (v w : QubitState) (h : v ≈ w) : blochRaw v = blochRaw w := by
  obtain ⟨z, hz, hvw⟩ := h
  have hz' : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]; norm_num
  have hzz : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, hz']; norm_num
  have hprod : (starRingEnd ℂ) (w.1 0) * w.1 1 = (starRingEnd ℂ) (v.1 0) * v.1 1 := by
    rw [hvw 0, hvw 1, map_mul]
    linear_combination ((starRingEnd ℂ) (v.1 0) * v.1 1) * hzz
  have hn0 : ‖w.1 0‖ = ‖v.1 0‖ := by rw [hvw 0, norm_mul, hz, one_mul]
  have hn1 : ‖w.1 1‖ = ‖v.1 1‖ := by rw [hvw 1, norm_mul, hz, one_mul]
  apply Sphere2.ext
  intro i
  fin_cases i <;>
    simp only [blochRaw, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, hprod, hn0, hn1]

/-- The Bloch map from pure states modulo phase to the 2-sphere. -/
