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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/
noncomputable def omegaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `n`-qubit quantum Fourier transform matrix, of size `2^n × 2^n`, with entries
`ω^(j*k) / √(2^n)` where `ω = exp(2πi/2^n)`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun j k => omegaN (2 ^ n) ^ ((j : ℕ) * (k : ℕ)) / Real.sqrt (2 ^ n)

lemma isPrimitiveRoot_omegaN {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (omegaN N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma omegaN_ne_zero (N : ℕ) : omegaN N ≠ 0 := Complex.exp_ne_zero _

lemma conj_omegaN (N : ℕ) : (starRingEnd ℂ) (omegaN N) = (omegaN N)⁻¹ := by
  rw [omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    Complex.conj_natCast]
  ring

/-- The key orthogonality relation between the columns of the Fourier matrix. -/
lemma sum_omegaN_pow {N : ℕ} (hN : N ≠ 0) (a b : Fin N) :
    ∑ k : Fin N, (omegaN N ^ ((k : ℕ) * (a : ℕ)))⁻¹ * omegaN N ^ ((k : ℕ) * (b : ℕ))
      = if a = b then (N : ℂ) else 0 := by
  have hprim := isPrimitiveRoot_omegaN hN
  have hne : ∀ m : ℕ, omegaN N ^ m ≠ 0 := fun m => pow_ne_zero _ (omegaN_ne_zero N)
  set z : ℂ := omegaN N ^ (b : ℕ) / omegaN N ^ (a : ℕ) with hz
  have hterm : ∀ k : ℕ, (omegaN N ^ (k * (a : ℕ)))⁻¹ * omegaN N ^ (k * (b : ℕ)) = z ^ k := by
    intro k
    have hswap : ∀ m : ℕ, omegaN N ^ (k * m) = (omegaN N ^ m) ^ k := by
      intro m; rw [← pow_mul, mul_comm]
    rw [hswap, hswap, hz, div_pow, div_eq_mul_inv, mul_comm]
  have hsum : ∑ k : Fin N, (omegaN N ^ ((k : ℕ) * (a : ℕ)))⁻¹ * omegaN N ^ ((k : ℕ) * (b : ℕ))
      = ∑ k ∈ Finset.range N, z ^ k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => z ^ k) N]
    exact Finset.sum_congr rfl fun k _ => hterm k
  rw [hsum]
  have hzN : z ^ N = 1 := by
    rw [hz, div_pow, ← pow_mul, ← pow_mul, mul_comm (b : ℕ) N, mul_comm (a : ℕ) N, pow_mul,
      pow_mul, hprim.pow_eq_one, one_pow, one_pow, div_one]
  by_cases hab : a = b
  · have hz1 : z = 1 := by rw [hz, hab, div_self (hne _)]
    simp [hz1, hab]
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hz, div_eq_one_iff_eq (hne _)] at h
      exact hab (Fin.ext (hprim.pow_inj b.isLt a.isLt h)).symm
    rw [geom_sum_eq hz1, hzN, if_neg hab, sub_self, zero_div]

lemma sqrt_two_pow_sq (n : ℕ) :
    ((Real.sqrt (2 ^ n) : ℝ) : ℂ) * ((Real.sqrt (2 ^ n) : ℝ) : ℂ) = ((2 ^ n : ℕ) : ℂ) := by
  have h : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hr := Real.mul_self_sqrt h
  push_cast
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hr

lemma sqrt_two_pow_ne_zero (n : ℕ) : ((Real.sqrt (2 ^ n) : ℝ) : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt (2 ^ n) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast h.ne'

/-- **The `n`-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hN : (2 : ℕ) ^ n ≠ 0 := by positivity
  have hcast : (((2 : ℕ) ^ n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have key : ∀ k : Fin (2 ^ n),
      (star (qft n)) a k * qft n k b
        = ((omegaN (2 ^ n) ^ ((k : ℕ) * (a : ℕ)))⁻¹ * omegaN (2 ^ n) ^ ((k : ℕ) * (b : ℕ)))
          / (((2 : ℕ) ^ n : ℕ) : ℂ) := by
    intro k
    rw [Matrix.star_apply, qft]
    simp only [Matrix.of_apply, Complex.star_def, map_div₀, map_pow, conj_omegaN,
      Complex.conj_ofReal, inv_pow]
    rw [div_mul_div_comm, sqrt_two_pow_sq]
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div, sum_omegaN_pow hN a b]
  rcases eq_or_ne a b with hab | hab
  · rw [if_pos hab, if_pos hab, div_self hcast]
  · rw [if_neg hab, if_neg hab, zero_div]

/-- Explicit form of unitarity: `Uᴴ * U = 1`. -/
theorem qft_conjTranspose_mul_self (n : ℕ) : (qft n)ᴴ * qft n = 1 :=
  (Matrix.mem_unitaryGroup_iff'.mp (qft_unitary n))

/-- Explicit form of unitarity: `U * Uᴴ = 1`. -/
theorem qft_mul_conjTranspose_self (n : ℕ) : qft n * (qft n)ᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff.mp (qft_unitary n))

end QC

