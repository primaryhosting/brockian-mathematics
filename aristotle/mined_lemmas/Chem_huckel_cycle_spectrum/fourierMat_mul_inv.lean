import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
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

namespace Chem

open Matrix Complex

/-! ## The `n`-th root of unity and its basic arithmetic -/

section Roots

variable (n : ℕ) [NeZero n]

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma fourierMat_mul_inv : fourierMat n * fourierMatInv n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hz : zeta n ≠ 0 := zeta_ne_zero n
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hpt : ∀ k : Fin n, fourierMat n j k * fourierMatInv n k l
      = (n : ℂ)⁻¹ * ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    have hpow : ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) ^ (k : ℕ)
        = (zeta n) ^ ((j : ℕ) * (k : ℕ)) * ((zeta n) ^ ((k : ℕ) * (l : ℕ)))⁻¹ := by
      rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm (l : ℕ) (k : ℕ)]
    simp only [fourierMat, fourierMatInv, Matrix.of_apply]
    rw [hpow]
    ring
  have hun : ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, zeta_pow_pow_n, zeta_pow_pow_n, inv_one, mul_one]
  rw [Finset.sum_congr rfl fun k _ => hpt k, ← Finset.mul_sum, sum_pow_val _ hun]
  have huiff : ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) = 1 ↔ j = l := by
    rw [mul_inv_eq_one₀ (pow_ne_zero _ hz)]
    exact ⟨zeta_pow_inj, fun h => by rw [h]⟩
  by_cases h : j = l
  · rw [if_pos (huiff.mpr h), if_pos h, inv_mul_cancel₀ hn0]
  · rw [if_neg (fun hc => h (huiff.mp hc)), if_neg h, mul_zero]

