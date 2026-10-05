/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `IsPrimitiveRootMod a p` says that the integer `a` is a primitive root modulo `p`, i.e.
the residue of `a` generates the multiplicative group `(ZMod p)ˣ`, which for a prime `p`
amounts to the multiplicative order of `a` in `ZMod p` being exactly `p - 1`. -/

lemma artin_iff_unbounded :
    ArtinPrimitiveRootConjecture ↔ ArtinPrimitiveRootUnbounded := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hlt⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hlt, hp.1, hp.2⟩
  · intro h a ha hsq
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp, hprim⟩ := h a ha hsq N
    exact ⟨p, ⟨hp, hprim⟩, hlt⟩

/-- **Artin's conjecture on primitive roots**, formalized, together with a Lean-checked
reduction and base cases.

* The first component is the reduction: the conjecture (stated as the infinitude, for each
  integer `a ≠ -1` that is not a perfect square, of the set of primes `p` with `a` a primitive
  root mod `p`) is equivalent to the statement that such primes occur beyond every bound.
* The second component verifies the base cases `p = 3, 5, 11, 13` for `a = 2`: the number `2`
  is a primitive root modulo each of these primes. -/
