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

lemma sum_E2 (a : ℕ) : 2 * (∑ i ∈ Finset.Icc (a + 1) (2 * a), i) = a * (3 * a + 1) := by
  have h := two_mul_sum_Icc (a := a + 1) (b := 2 * a) (by omega)
  simp only [Nat.add_sub_cancel] at h
  nlinarith [h]

