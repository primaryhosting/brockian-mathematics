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

