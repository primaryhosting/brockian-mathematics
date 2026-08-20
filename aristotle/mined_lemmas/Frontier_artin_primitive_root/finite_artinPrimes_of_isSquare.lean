import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

lemma finite_artinPrimes_of_isSquare {a : ℤ} (ha : IsSquare a) :
    (artinPrimes a).Finite :=
  Set.Finite.subset (Set.finite_singleton 2) (artinPrimes_subset_of_isSquare ha)

/-- `-1` is a primitive root only modulo `2` and `3`. -/
