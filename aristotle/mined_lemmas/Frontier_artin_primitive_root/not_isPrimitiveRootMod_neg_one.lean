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

theorem not_isPrimitiveRootMod_neg_one {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have hsq : (((-1 : ℤ) : ZMod p)) ^ 2 = 1 := by push_cast; ring
  have hdvd : orderOf (((-1 : ℤ) : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hle : orderOf (((-1 : ℤ) : ZMod p)) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  rw [h] at hle
  omega

/-- The exceptional set for a perfect square: at most the prime `2`. -/
