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

lemma finite_artinPrimes_neg_one : (artinPrimes (-1)).Finite :=
  Set.Finite.subset (Set.toFinite _) artinPrimes_neg_one_subset

/-- Every prime admits *some* primitive root: the unconditional weak form of Artin's
conjecture. -/
