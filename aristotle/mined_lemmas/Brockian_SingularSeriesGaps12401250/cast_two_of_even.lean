import Mathlib

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

/-- A finite set of integers is *admissible* (in the sense of the prime `k`-tuples
conjecture) if for every prime `p` it fails to cover all residue classes modulo `p`. -/

lemma cast_two_of_even {h : ℕ} (he : Even h) : ((h : ℤ) : ZMod 2) = 0 := by
  obtain ⟨k, hk⟩ := he
  subst hk
  push_cast
  ring_nf
  simp
  right
  rfl

/-- For odd `h`, the gap `h` reduces to `1` modulo `2`. -/
