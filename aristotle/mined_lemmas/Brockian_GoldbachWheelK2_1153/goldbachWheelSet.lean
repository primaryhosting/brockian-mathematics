import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153


noncomputable def goldbachWheelSet (M : ℕ) [NeZero M] (n : ZMod M) : Finset (ZMod M) :=
  Finset.univ.filter (fun r => IsUnit r ∧ IsUnit (n - r))

