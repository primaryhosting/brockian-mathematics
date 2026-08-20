import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
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

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when its residue class generates the
multiplicative group of `ZMod p`, i.e. when it has multiplicative order `p - 1`. -/

lemma sq_not_primitiveRoot (a : ℤ) (ha : IsSquare a) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  intro h
  rw [IsPrimitiveRootMod, show (((b * b : ℤ) : ZMod p)) = (b : ZMod p) ^ 2 by push_cast; ring] at h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hodd
    have := hp.two_le
    omega
  have hb : ((b : ZMod p)) ≠ 0 := by
    intro hb0
    rw [hb0] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, orderOf_zero] at h
    omega
  have key : ((b : ZMod p) ^ 2) ^ ((p - 1) / 2) = 1 := by
    rw [← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by obtain ⟨k, hk⟩ := hodd; omega]
    exact ZMod.pow_card_sub_one_eq_one hb
  have hdvd := orderOf_dvd_of_pow_eq_one key
  rw [h] at hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The second exclusion in Artin's conjecture is necessary: `-1` has order `2`, hence is
not a primitive root modulo any prime `p > 3`. -/
