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

def ArtinPrimitiveRootConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Infinite

/-- The "unbounded" form of Artin's conjecture: for every admissible `a` and every bound `N`
there is a prime `p > N` having `a` as a primitive root. -/
