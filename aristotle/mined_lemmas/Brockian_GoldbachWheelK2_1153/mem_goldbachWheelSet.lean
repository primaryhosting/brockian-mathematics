import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153


lemma mem_goldbachWheelSet {M : ℕ} [NeZero M] {n r : ZMod M} :
    r ∈ goldbachWheelSet M n ↔ IsUnit r ∧ IsUnit (n - r) := by
  simp [goldbachWheelSet]

/-- Over a prime modulus the wheel set is the complement of `{0, n}`. -/
