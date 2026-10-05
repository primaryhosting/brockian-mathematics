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

lemma coeff_prod_finset (s : Finset ℕ) (n : ℕ) (hs : Finset.range n ⊆ s) :
    (PowerSeries.coeff n) (∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card := by
  have himg : ∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1))
      = ∏ j ∈ s.image (fun i => i + 1), (1 - (X : ℤ⟦X⟧) ^ j) := by
    rw [Finset.prod_image (fun a _ b _ h => by omega)]
  rw [himg]
  refine coeff_prod_shifted _ _ (fun h => ?_) (fun x hx => ?_)
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
    omega
  · rw [Finset.mem_Icc] at hx
    refine Finset.mem_image.2 ⟨x - 1, hs (Finset.mem_range.2 (by omega)), by omega⟩

