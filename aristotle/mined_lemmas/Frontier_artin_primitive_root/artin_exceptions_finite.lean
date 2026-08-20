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

theorem artin_exceptions_finite {a : ℤ} (ha : IsSquare a ∨ a = -1) :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Finite := by
  rcases ha with ha | rfl
  · exact Set.Finite.subset (Set.finite_singleton 2) (isSquare_primes_subset ha)
  · exact Set.Finite.subset (Set.toFinite _) neg_one_primes_subset

/-- Base case: `2` is a primitive root modulo `3`, `5`, `11`, `13`, `19` and `29`. -/
