import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

A partition of `n` into distinct positive parts is encoded as a `Finset ℕ` not containing `0`
whose sum is `n`.  The main result of this file, `Franklin.sum_sign_DP`, is Franklin's theorem:
the signed count `∑ (-1)^(number of parts)` over all partitions of `n` into distinct parts is
`(-1)^k` if `n` is a generalized pentagonal number `k(3k∓1)/2`, and `0` otherwise.
-/

namespace Franklin

open Finset

/-- Partitions of `n` into distinct positive parts, encoded as finsets of positive naturals. -/

theorem sum_sign_DP (n : ℕ) : (∑ s ∈ DP n, (-1 : ℤ) ^ s.card) = pentSign n := by
  classical
  have hsplit1 : (∑ s ∈ (DP n).filter IsA, (-1 : ℤ) ^ s.card)
      + ∑ s ∈ (DP n).filter (fun s => ¬IsA s), (-1 : ℤ) ^ s.card
      = ∑ s ∈ DP n, (-1 : ℤ) ^ s.card :=
    Finset.sum_filter_add_sum_filter_not (DP n) IsA _
  have hsplit2 : (∑ s ∈ ((DP n).filter (fun s => ¬IsA s)).filter IsB, (-1 : ℤ) ^ s.card)
      + ∑ s ∈ ((DP n).filter (fun s => ¬IsA s)).filter (fun s => ¬IsB s), (-1 : ℤ) ^ s.card
      = ∑ s ∈ (DP n).filter (fun s => ¬IsA s), (-1 : ℤ) ^ s.card :=
    Finset.sum_filter_add_sum_filter_not _ IsB _
  have hB : ((DP n).filter (fun s => ¬IsA s)).filter IsB = (DP n).filter IsB := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro s _
    simp only [eq_iff_iff, and_iff_right_iff_imp]
    exact fun h => not_isA_of_isB h
  have hX : ((DP n).filter (fun s => ¬IsA s)).filter (fun s => ¬IsB s)
      = (DP n).filter (fun s => ¬IsA s ∧ ¬IsB s) := Finset.filter_filter _ _ _
  rw [← hsplit1, ← hsplit2, hB, hX, exc_eq n, Finset.sum_union (X1_disjoint_X2 n), sum_X1, sum_X2,
    ← add_assoc, sum_A_add_sum_B n, zero_add, pentSign]

end Exceptional

end Franklin

import Mathlib
import RequestProject.Franklin

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 2000000

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-- The coefficient sequence of the pentagonal number series
`∑ k, (-1)^k (X^(k(3k-1)/2) + X^(k(3k+1)/2))`, indexed by the generalized pentagonal numbers.
The value at `n` is `(-1)^k` if `n = k(3k-1)/2` or `n = k(3k+1)/2` for some `k`, and `0`
otherwise. -/
