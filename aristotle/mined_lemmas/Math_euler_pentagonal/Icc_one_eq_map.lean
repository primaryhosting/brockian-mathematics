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

lemma Icc_one_eq_map (n : ℕ) :
    Finset.Icc 1 n = (Finset.range n).map ⟨fun k => k + 1, add_left_injective 1⟩ := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x - 1, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    omega

