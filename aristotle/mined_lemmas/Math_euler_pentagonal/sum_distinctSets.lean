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

theorem sum_distinctSets (n : ℕ) :
    ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card = pentSign n := by
  have h := Finset.sum_filter_add_sum_filter_not (distinctSets n) (fun S => IsExc S)
    (fun S => ((-1 : ℤ)) ^ S.card)
  rw [← h, ← excSets, ← nonExcSets, sum_nonExc, sum_exc, add_zero]

/-! ## Passing to generating functions -/

