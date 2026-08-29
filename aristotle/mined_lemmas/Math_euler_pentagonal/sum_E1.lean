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

lemma sum_E1 (a : ℕ) (ha : 1 ≤ a) : 2 * (∑ i ∈ Finset.Icc a (2 * a - 1), i) = a * (3 * a - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have h := two_mul_sum_Icc (a := k + 1) (b := 2 * (k + 1) - 1) (by omega)
  have e0 : 2 * (k + 1) - 1 + 1 = 2 * k + 2 := by omega
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
  have e3 : k + 1 - 1 = k := by omega
  rw [e0, e1, e3] at h
  rw [e1, e2]
  nlinarith [h]

