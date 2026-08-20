/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` has
multiplicative order exactly `p - 1`, i.e. it generates the group `(ZMod p)ˣ`. -/

theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  intro h
  set x : ZMod p := ((b * b : ℤ) : ZMod p) with hx
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpow : x ^ (p - 1) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h] at this
  have hb : ((b : ZMod p)) ≠ 0 := by
    intro hb0
    apply (one_ne_zero (α := ZMod p))
    rw [← hpow, hx]
    push_cast
    have hne : p - 1 ≠ 0 := by omega
    rw [hb0]
    simp [hne]
  -- write `p - 1 = 2 * q`
  obtain ⟨q, hq⟩ : ∃ q, p - 1 = 2 * q := by
    have hodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hq0 : 0 < q := by omega
  have hxq : x ^ q = 1 := by
    have hbb : x = (b : ZMod p) ^ 2 := by rw [hx]; push_cast; ring
    rw [hbb, ← pow_mul]
    have : 2 * q = p - 1 := hq.symm
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one hb
  have hdvd : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one hxq
  have hle : orderOf x ≤ q := Nat.le_of_dvd hq0 hdvd
  rw [h] at hle
  omega

/-- `-1` is a primitive root only modulo `2` and `3`: for `p > 3` its order is at most `2`. -/
