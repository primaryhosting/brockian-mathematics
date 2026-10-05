import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
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

namespace QC

/-- The `n`-dimensional quantum Fourier transform matrix:
`(qftMatrix n) i j = exp (2 π I * (i * j) / n) / √n`.
For `n = 2 ^ 7` this is the 7-qubit QFT. -/

theorem qftMatrix_unitary {n : ℕ} (hn : n ≠ 0) :
    qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsq : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    simp
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin n, qftMatrix n i k * (star (qftMatrix n)) k j
      = (qftRoot n ^ (i : ℕ) * (qftRoot n ^ (j : ℕ))⁻¹) ^ (k : ℕ) / n := by
    intro k
    have h1 : qftMatrix n i k = qftRoot n ^ ((i : ℕ) * (k : ℕ)) / (Real.sqrt n : ℝ) :=
      qftMatrix_apply i k
    have h2 : (star (qftMatrix n)) k j
        = (qftRoot n ^ ((j : ℕ) * (k : ℕ)))⁻¹ / (Real.sqrt n : ℝ) := by
      rw [Matrix.star_apply, qftMatrix_apply, Complex.star_def, map_div₀, conj_qftRoot_pow,
        Complex.conj_ofReal]
    rw [h1, h2, div_mul_div_comm, hsq]
    congr 1
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div, qft_geom_sum hn i j]
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, hnC]

/-- The 7-qubit quantum Fourier transform matrix is unitary. -/
