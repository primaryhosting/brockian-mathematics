import Mathlib

/-!
# Wilson
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.wilson
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

namespace NumberTheory

/-- Key intermediate lemma: the product of all units of `ZMod p`, viewed in `ZMod p`,
equals `-1`. This is the group-theoretic heart of Wilson's theorem: in the cyclic
group `(ZMod p)ˣ`, pairing each unit with its inverse leaves only the elements of
order at most two, whose product is `-1`. -/

theorem factorial_cast_eq_prod_units (p : ℕ) [Fact (Nat.Prime p)] :
    (((p - 1)! : ℕ) : ZMod p) = ∏ x : (ZMod p)ˣ, (x : ZMod p) := by
  rw [ZMod.wilsons_lemma, prod_units_eq_neg_one]

/-- **Wilson's theorem**: for a prime `p`, `(p - 1)!` is congruent to `-1` modulo `p`. -/
