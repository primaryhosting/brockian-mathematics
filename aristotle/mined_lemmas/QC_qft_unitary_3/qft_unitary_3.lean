/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

open Complex

/-- The primitive 8-th root of unity `exp(2πi/8)`. -/

theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 8,
      (star qft3) a k * qft3 k b = (omega8 ^ (7 * (a : ℕ) + (b : ℕ))) ^ (k : ℕ) / 8 := by
    intro k
    rw [Matrix.star_apply]
    show (starRingEnd ℂ) (qft3 k a) * qft3 k b = _
    simp only [qft3, Matrix.of_apply, map_div₀, map_pow, conj_omega8,
      Complex.conj_ofReal]
    rw [div_mul_div_comm, sqrt8_sq, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    ring
  simp only [key]
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun k => (omega8 ^ (7 * (a : ℕ) + (b : ℕ))) ^ k) 8]
  rw [sum_omega8_pow]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : a = b
  · subst hab
    have : (8 : ℕ) ∣ 7 * (a : ℕ) + (a : ℕ) := ⟨(a : ℕ), by ring⟩
    simp [this]
  · have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    have : ¬ (8 : ℕ) ∣ 7 * (a : ℕ) + (b : ℕ) := by omega
    simp [this, hab]

/-- The QFT matrix satisfies `Qᴴ * Q = 1`. -/
