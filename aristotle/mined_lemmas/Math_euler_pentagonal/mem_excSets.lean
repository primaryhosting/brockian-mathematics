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

lemma mem_excSets {n : ℕ} {S : Finset ℕ} :
    S ∈ excSets n ↔ (0 ∉ S ∧ ∑ i ∈ S, i = n ∧ IsExc S) := by
  rw [excSets, Finset.mem_filter, mem_distinctSets]
  tauto

