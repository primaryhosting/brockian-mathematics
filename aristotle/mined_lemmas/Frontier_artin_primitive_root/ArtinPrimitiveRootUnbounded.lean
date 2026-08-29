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

def ArtinPrimitiveRootUnbounded : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPrimitiveRootMod a p

section BaseCases

