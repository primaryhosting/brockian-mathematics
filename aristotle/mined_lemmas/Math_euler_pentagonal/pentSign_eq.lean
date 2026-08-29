import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma pentSign_eq {n : ℕ} (hn : n ≠ 0) :
    pentSign n = (∑ a ∈ Finset.Icc 1 n, (if 2 * n = a * (3 * a - 1) then ((-1 : ℤ)) ^ a else 0))
      + ∑ a ∈ Finset.Icc 1 n, (if 2 * n = a * (3 * a + 1) then ((-1 : ℤ)) ^ a else 0) := by
  rw [pentSign, if_neg hn, zero_add]

