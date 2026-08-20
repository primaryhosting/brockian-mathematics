/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The primitive `n`-th root of unity `exp (2πi / n)` used to build the QFT matrix. -/

theorem qftMatrix_mem_unitaryGroup (n : ℕ) (hn : n ≠ 0) :
    qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hsq : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnpos.le, Complex.ofReal_natCast]
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n,
      qftMatrix n j k * (star (qftMatrix n)) k l
        = (qftRoot n ^ (j : ℕ) * (qftRoot n)⁻¹ ^ (l : ℕ)) ^ (k : ℕ) / (n : ℂ) := by
    intro k
    simp only [qftMatrix, Matrix.of_apply, Matrix.star_apply, Complex.star_def, map_div₀,
      map_pow, conj_qftRoot, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) (k : ℕ),
      mul_comm (l : ℕ) (k : ℕ), pow_mul, pow_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, qft_geom_sum n hn j l]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases h : j = l
  · simp [h, hnC]
  · simp [h]

/-- The 6-qubit quantum Fourier transform matrix (of size `2^6 = 64`) is unitary. -/
