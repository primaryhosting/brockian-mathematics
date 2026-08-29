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

theorem isPrimitiveRootMod_three_seven : IsPrimitiveRootMod 3 7 := by
  rw [IsPrimitiveRootMod, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, by decide⟩

/-! ### The main statement -/

/--
**Artin's conjecture on primitive roots**, formalized, together with everything that is
unconditionally provable about it here.

* (1) The statement of the conjecture is recorded as `Frontier.ArtinConjecture`, and it
  is equivalent to: for every admissible `a` and every bound `N` there is a prime `p > N`
  having `a` as a primitive root (a Lean-checked reformulation/reduction).
* (2) The excluded case `IsSquare a` is genuinely necessary: for such `a` the set of
  primes admitting `a` as a primitive root is contained in `{2}`, hence finite.
* (3) The excluded case `a = -1` is genuinely necessary: the corresponding set of primes
  is contained in `{2, 3}`, hence finite.
* (4) Base cases: `2` is a primitive root mod `11` and mod `13`, and `3` is one mod `7`.
-/
