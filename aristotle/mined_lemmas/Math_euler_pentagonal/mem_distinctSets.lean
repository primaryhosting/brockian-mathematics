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

lemma mem_distinctSets {n : ℕ} {S : Finset ℕ} :
    S ∈ distinctSets n ↔ (0 ∉ S ∧ ∑ i ∈ S, i = n) := by
  simp only [distinctSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun x hx => ?_, hsum⟩
    have h1 : 1 ≤ x := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact h0 hx)
    have h2 : x ≤ n := hsum ▸ Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp [Finset.mem_Icc, h1, h2]

/-- The coefficient predicted by Euler's pentagonal number theorem. -/
