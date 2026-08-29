/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Math2

/-- The affine plane curve `C(m,n) = {(x,y) | y ^ n = x ^ m}`. -/

lemma range_monomialParam {k : Type*} [Field k] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : Nat.Coprime m n) : Set.range (monomialParam k m n) = monomialCurve k m n := by
  ext ⟨x, y⟩
  simp only [Set.mem_range, monomialCurve, Set.mem_setOf_eq, monomialParam, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht1, ht2⟩
    rw [← ht1, ← ht2, ← pow_mul, ← pow_mul, Nat.mul_comm]
  · intro hxy
    by_cases hx : x = 0
    · subst hx
      have hy : y = 0 := by
        have : y ^ n = 0 := by simpa [zero_pow hm.ne'] using hxy
        exact (pow_eq_zero_iff hn.ne').1 this
      exact ⟨0, by simp [zero_pow hn.ne', zero_pow hm.ne', hy]⟩
    · have hy : y ≠ 0 := by
        intro hy
        apply hx
        have : x ^ m = 0 := by rw [← hxy, hy, zero_pow hn.ne']
        exact (pow_eq_zero_iff hm.ne').1 this
      set a : ℤ := Nat.gcdA m n with ha
      set b : ℤ := Nat.gcdB m n with hb
      have hgcd : (1 : ℤ) = (m : ℤ) * a + (n : ℤ) * b := by
        have hab := Nat.gcd_eq_gcd_ab m n
        rw [Nat.Coprime.gcd_eq_one h] at hab
        exact_mod_cast hab
      have hxy' : y ^ (n : ℤ) = x ^ (m : ℤ) := by
        rw [zpow_natCast, zpow_natCast]; exact hxy
      refine ⟨x ^ b * y ^ a, ?_, ?_⟩
      · calc (x ^ b * y ^ a) ^ n
            = (x ^ b) ^ (n : ℤ) * (y ^ a) ^ (n : ℤ) := by
              rw [← zpow_natCast (x ^ b * y ^ a) n, mul_zpow]
          _ = x ^ ((n : ℤ) * b) * (y ^ (n : ℤ)) ^ a := by
              rw [← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm b (n : ℤ), mul_comm a (n : ℤ)]
          _ = x ^ ((n : ℤ) * b) * x ^ ((m : ℤ) * a) := by rw [hxy', ← zpow_mul]
          _ = x ^ ((m : ℤ) * a + (n : ℤ) * b) := by rw [← zpow_add₀ hx]; ring_nf
          _ = x := by rw [← hgcd, zpow_one]
      · calc (x ^ b * y ^ a) ^ m
            = (x ^ b) ^ (m : ℤ) * (y ^ a) ^ (m : ℤ) := by
              rw [← zpow_natCast (x ^ b * y ^ a) m, mul_zpow]
          _ = (x ^ (m : ℤ)) ^ b * y ^ ((m : ℤ) * a) := by
              rw [← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm b (m : ℤ), mul_comm a (m : ℤ)]
          _ = (y ^ (n : ℤ)) ^ b * y ^ ((m : ℤ) * a) := by rw [hxy']
          _ = y ^ ((m : ℤ) * a + (n : ℤ) * b) := by rw [← zpow_mul, ← zpow_add₀ hy]; ring_nf
          _ = y := by rw [← hgcd, zpow_one]

/-- The defining polynomial `Y ^ n - X ^ m` of the curve `C(m,n)`, as a polynomial in the two
variables `X 0 = X` and `X 1 = Y`. -/
