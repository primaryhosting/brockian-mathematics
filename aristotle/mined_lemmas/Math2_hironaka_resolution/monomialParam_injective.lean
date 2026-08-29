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

lemma monomialParam_injective {k : Type*} [Field k] {m n : ℕ} (hn : 0 < n)
    (h : Nat.Coprime m n) : Function.Injective (monomialParam k m n) := by
  intro t s hts
  simp only [monomialParam, Prod.mk.injEq] at hts
  obtain ⟨hn', hm'⟩ := hts
  by_cases ht : t = 0
  · subst ht
    have : s ^ n = 0 := by simpa [zero_pow hn.ne'] using hn'.symm
    exact ((pow_eq_zero_iff hn.ne').1 this).symm
  · have hs : s ≠ 0 := by
      intro hs
      apply ht
      have : t ^ n = 0 := by simp [hn', hs, zero_pow hn.ne']
      exact (pow_eq_zero_iff hn.ne').1 this
    have hu : t * s⁻¹ ≠ 0 := mul_ne_zero ht (inv_ne_zero hs)
    have hum : (t * s⁻¹) ^ m = 1 := by
      rw [mul_pow, hm', inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs)]
    have hun : (t * s⁻¹) ^ n = 1 := by
      rw [mul_pow, hn', inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs)]
    have := eq_one_of_coprime_pow h hu hum hun
    field_simp at this
    exact this

