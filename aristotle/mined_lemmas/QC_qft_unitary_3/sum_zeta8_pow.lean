import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

/-- The primitive 8-th root of unity `exp (2 π i / 8)`. -/

lemma sum_zeta8_pow (n : ℕ) (h : ¬ (8 ∣ n)) :
    ∑ m : Fin 8, (zeta8 ^ n) ^ (m : ℕ) = 0 := by
  have hx : zeta8 ^ n ≠ 1 := fun hc => h ((zeta8_pow_eq_one_iff n).1 hc)
  have hpow : (zeta8 ^ n) ^ (8 : ℕ) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta8_pow_eight, one_pow]
  rw [Fin.sum_univ_eq_sum_range (fun m => (zeta8 ^ n) ^ m) 8, geom_sum_eq hx, hpow]
  simp

/-- The 3-qubit quantum Fourier transform matrix, acting on `Fin 8` basis states. -/
