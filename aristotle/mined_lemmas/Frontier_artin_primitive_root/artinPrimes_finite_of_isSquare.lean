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

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. when the multiplicative order of `a` in `ZMod p`
equals `p - 1`. -/

theorem artinPrimes_finite_of_isSquare {a : ℤ} (ha : IsSquare a) :
    (artinPrimes a).Finite :=
  Set.Finite.subset (Set.finite_singleton 2) (artinPrimes_subset_of_isSquare ha)

/-! ### Necessity of the hypothesis "`a ≠ -1`" -/

/-- `-1` has order at most `2`, so it is not a primitive root modulo any prime `p ≥ 5`. -/
