import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
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

open Complex Finset

/-- The root of unity `exp (2 π i / N)`. -/

lemma sum_omega_pow_mul_conj {N : ℕ} (hN : N ≠ 0) (j l : Fin N) :
    ∑ k : Fin N, omega N ^ ((j : ℕ) * (k : ℕ)) *
        (starRingEnd ℂ) (omega N ^ ((l : ℕ) * (k : ℕ))) =
      if j = l then (N : ℂ) else 0 := by
  have hne : omega N ^ (l : ℕ) ≠ 0 := pow_ne_zero _ (omega_ne_zero N)
  set z : ℂ := omega N ^ (j : ℕ) / omega N ^ (l : ℕ) with hz
  have h1 : (starRingEnd ℂ) (omega N ^ (l : ℕ)) = (omega N ^ (l : ℕ))⁻¹ := by
    rw [map_pow, conj_omega, inv_pow]
  have hterm : ∀ k : Fin N,
      omega N ^ ((j : ℕ) * (k : ℕ)) *
        (starRingEnd ℂ) (omega N ^ ((l : ℕ) * (k : ℕ))) = z ^ (k : ℕ) := by
    intro k
    rw [pow_mul, pow_mul, map_pow, h1, inv_pow, ← div_eq_mul_inv, hz, div_pow]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Fin.sum_univ_eq_sum_range (fun k => z ^ k) N]
  have hprim := isPrimitiveRoot_omega hN
  by_cases hjl : j = l
  · have hz1 : z = 1 := by rw [hz, hjl, div_self hne]
    simp [hz1, hjl]
  · have hzne : z ≠ 1 := by
      intro h
      rw [hz, div_eq_one_iff_eq hne] at h
      exact hjl (Fin.val_injective (hprim.pow_inj j.isLt l.isLt h))
    have hzN : z ^ N = 1 := by
      rw [hz, div_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) N, mul_comm (l : ℕ) N,
        pow_mul, pow_mul, hprim.pow_eq_one, one_pow, one_pow, div_one]
    rw [geom_sum_eq hzne, hzN]
    simp [hjl]

/-- The `n`-qubit quantum Fourier transform matrix:
`(QFT_n)_{j,k} = exp (2 π i j k / 2^n) / √(2^n)` acting on the `2^n`-dimensional
state space of `n` qubits. -/
