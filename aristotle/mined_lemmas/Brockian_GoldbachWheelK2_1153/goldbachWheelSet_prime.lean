import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153


lemma goldbachWheelSet_prime (p : ℕ) [Fact (Nat.Prime p)] (n : ZMod p) :
    goldbachWheelSet p n = Finset.univ \ ({0, n} : Finset (ZMod p)) := by
  ext r
  simp only [mem_goldbachWheelSet, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, isUnit_iff_ne_zero, sub_ne_zero, not_or]
  tauto

/-- Size of the `K = 2` Goldbach wheel at a prime modulus `p`: it has `p - 1` elements when
`p ∣ n` and `p - 2` elements otherwise. -/
