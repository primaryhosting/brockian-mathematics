import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
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

namespace Brockian

/-- The wheel modulus of this instance. -/

theorem GoldbachWheelK2_1051_zmod (x : ZMod wheelModulus1051) (N : ℕ) :
    ∃ p q : ℕ, N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
      ((p : ZMod wheelModulus1051) + (q : ZMod wheelModulus1051)) = x := by
  obtain ⟨p, q, hpN, hqN, hp, hq, h⟩ := GoldbachWheelK2_1051 x.val N
  refine ⟨p, q, hpN, hqN, hp, hq, ?_⟩
  have hcast : ((p + q : ℕ) : ZMod wheelModulus1051) = ((x.val : ℕ) : ZMod wheelModulus1051) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have : NeZero wheelModulus1051 := ⟨by unfold wheelModulus1051; norm_num⟩
  simpa using hcast

end Brockian

