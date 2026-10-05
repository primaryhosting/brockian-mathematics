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

lemma two_mul_sum_Icc {a b : ℕ} (h : a ≤ b + 1) :
    2 * (∑ i ∈ Finset.Icc a b, i) + a * (a - 1) = (b + 1) * b := by
  have hcons := Finset.sum_Ico_consecutive (fun i => i) (Nat.zero_le a) h
  rw [Finset.Ico_add_one_right_eq_Icc] at hcons
  have h1 := Finset.sum_range_id_mul_two a
  have h2 := Finset.sum_range_id_mul_two (b + 1)
  simp only [Nat.add_sub_cancel] at h2
  simp only [Finset.range_eq_Ico] at h1 h2 ⊢
  simp only at hcons
  omega

