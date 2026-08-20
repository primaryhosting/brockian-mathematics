import Mathlib

/-!
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
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

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/

lemma sum_e_mul (k : ZMod 5) : ∑ x : ZMod 5, e (k * x) = if k = 0 then 5 else 0 := by
  have hval : ∀ x : ZMod 5, e (k * x) = (e k) ^ x.val := by
    intro x
    simp only [e, ← pow_mul]
    rw [ZMod.val_mul, omega_pow_mod]
  rw [Finset.sum_congr rfl (fun x _ => hval x)]
  have hrange : ∑ x : ZMod 5, (e k) ^ x.val = ∑ j ∈ Finset.range 5, (e k) ^ j :=
    Fin.sum_univ_eq_sum_range (fun j => (e k) ^ j) 5
  rw [hrange]
  by_cases hk : k = 0
  · subst hk
    simp [e_zero]
  · have hne : e k ≠ 1 := by
      intro h
      apply hk
      have : omega ^ k.val = 1 := h
      have hdvd : (5 : ℕ) ∣ k.val := (isPrimitiveRoot_omega.pow_eq_one_iff_dvd k.val).1 this
      have hlt : k.val < 5 := ZMod.val_lt k
      have hz : k.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact (ZMod.val_eq_zero k).1 hz
    have hpow : (e k) ^ 5 = 1 := by
      simp only [e, ← pow_mul, mul_comm]
      rw [pow_mul, omega_pow_five, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]
    simp [hk]

/-- The complex-valued core Parseval identity. -/
