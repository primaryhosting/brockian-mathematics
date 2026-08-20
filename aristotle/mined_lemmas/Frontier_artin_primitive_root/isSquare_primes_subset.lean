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

theorem isSquare_primes_subset {a : ℤ} (ha : IsSquare a) :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p} ⊆ {2} := by
  intro p hp
  by_contra hne
  exact not_isPrimitiveRootMod_of_isSquare ha hp.1 (by simpa using hne) hp.2

/-- The exceptional set for `-1`: at most the primes `2` and `3`. -/
