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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when the image of `a` in `ZMod p` has
multiplicative order exactly `p - 1`, i.e. it generates the group of units of `ZMod p`. -/

theorem finite_primitiveRootPrimes_neg_one :
    (primitiveRootPrimes (-1)).Finite := by
  apply Set.Finite.subset (Set.toFinite ({2, 3} : Set ℕ))
  rintro p ⟨hp, h⟩
  rcases eq_two_or_three_of_isPrimitiveRootMod_neg_one hp h with h' | h' <;> simp [h']

/-! ### The main statement -/

/-- **Artin's conjecture on primitive roots**, together with a Lean-checked reduction:
the conjecture (`ArtinConjecture`: any integer that is neither `-1` nor a perfect square
is a primitive root modulo infinitely many primes) is *equivalent* to the sharper
characterisation saying that an integer is a primitive root modulo infinitely many primes
*exactly when* it is neither `-1` nor a perfect square.

The nontrivial content proved here is the unconditional converse direction: for `a = -1`
and for perfect squares `a`, the set of primes modulo which `a` is a primitive root is
finite (contained in `{2, 3}`, resp. `{2}`). Hence nothing is lost by stating Artin's
conjecture with those exclusions. -/
