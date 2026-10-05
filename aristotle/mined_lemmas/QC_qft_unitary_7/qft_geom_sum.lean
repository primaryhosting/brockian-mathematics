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

theorem qft_geom_sum {n : ℕ} (hn : n ≠ 0) (i j : Fin n) :
    ∑ k : Fin n, (qftRoot n ^ (i : ℕ) * (qftRoot n ^ (j : ℕ))⁻¹) ^ (k : ℕ)
      = if i = j then (n : ℂ) else 0 := by
  set z := qftRoot n with hz
  set w : ℂ := z ^ (i : ℕ) * (z ^ (j : ℕ))⁻¹ with hw
  have hzne : z ≠ 0 := qftRoot_ne_zero n
  have hzn : z ^ n = 1 := (qftRoot_isPrimitiveRoot hn).pow_eq_one
  rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k) n]
  by_cases hij : i = j
  · have hw1 : w = 1 := by
      rw [hw, hij]
      field_simp
    simp [hw1, hij]
  · have hw1 : w ≠ 1 := by
      intro h
      apply hij
      have hpow : z ^ (i : ℕ) = z ^ (j : ℕ) := by
        rw [hw] at h
        field_simp at h
        exact h
      exact Fin.ext ((qftRoot_isPrimitiveRoot hn).pow_inj i.isLt j.isLt hpow)
    have hwn : w ^ n = 1 := by
      rw [hw, mul_pow, ← pow_mul, ← inv_pow, ← pow_mul, mul_comm (i : ℕ) n,
        mul_comm (j : ℕ) n, pow_mul, pow_mul, hzn]
      simp [hzn]
    rw [geom_sum_eq hw1, hwn]
    simp [hij]

/-- The `n`-dimensional QFT matrix is unitary (for `n ≠ 0`). -/
