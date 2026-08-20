import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when its residue class generates the
multiplicative group of `ZMod p`, i.e. when it has multiplicative order `p - 1`. -/

lemma finite_primes_primitiveRoot_of_isSquare (a : ℤ) (ha : IsSquare a) :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton 2) ?_
  rintro p ⟨hp, hpr⟩
  by_contra hne
  exact sq_not_primitiveRoot a ha p hp hne hpr

/-- The set of primes having `-1` as a primitive root is contained in `{2, 3}`, hence
finite: Artin's conjecture genuinely fails for `a = -1`. -/
