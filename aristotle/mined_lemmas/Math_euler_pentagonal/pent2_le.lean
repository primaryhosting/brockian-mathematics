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

lemma pent2_le {a n : ℕ} (ha : 1 ≤ a) (h : 2 * n = a * (3 * a + 1)) : a ≤ n := by
  nlinarith

/-! ### Evaluating the exceptional sum -/

