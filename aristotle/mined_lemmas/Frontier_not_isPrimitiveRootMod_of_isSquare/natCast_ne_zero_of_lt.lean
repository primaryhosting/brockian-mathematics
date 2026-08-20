/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` if every nonzero residue class mod `p`
is a power of `a`, i.e. `a` generates the multiplicative group `(ZMod p)ˣ`. -/

private lemma natCast_ne_zero_of_lt {p k : ℕ} (hk : 0 < k) (hkp : k < p) :
    ((k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hk hkp

/-- A perfect square is never a primitive root modulo an odd prime: all its powers are
squares, while an odd prime field always contains a non-square. -/
