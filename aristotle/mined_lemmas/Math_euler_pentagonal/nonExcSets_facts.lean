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

lemma nonExcSets_facts {n : ℕ} {S : Finset ℕ} (hS : S ∈ nonExcSets n) :
    S.Nonempty ∧ 0 ∉ S ∧ ∑ i ∈ S, i = n ∧ ¬ IsExc S := by
  obtain ⟨h0, hsum, hexc⟩ := mem_nonExcSets.1 hS
  refine ⟨?_, h0, hsum, hexc⟩
  rcases Finset.eq_empty_or_nonempty S with rfl | h
  · exact absurd (Or.inl rfl) hexc
  · exact h

