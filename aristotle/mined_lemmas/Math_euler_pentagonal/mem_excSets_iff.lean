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

lemma mem_excSets_iff {n : ℕ} {S : Finset ℕ} :
    S ∈ excSets n ↔ (S = ∅ ∧ n = 0)
      ∨ (∃ a, 1 ≤ a ∧ 2 * n = a * (3 * a - 1) ∧ S = Finset.Icc a (2 * a - 1))
      ∨ (∃ a, 1 ≤ a ∧ 2 * n = a * (3 * a + 1) ∧ S = Finset.Icc (a + 1) (2 * a)) := by
  rw [mem_excSets]
  constructor
  · rintro ⟨h0, hsum, (rfl | ⟨a, ha, rfl | rfl⟩)⟩
    · exact Or.inl ⟨rfl, by simpa using hsum.symm⟩
    · refine Or.inr (Or.inl ⟨a, ha, ?_, rfl⟩)
      have := sum_E1 a ha
      omega
    · refine Or.inr (Or.inr ⟨a, ha, ?_, rfl⟩)
      have := sum_E2 a
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨a, ha, h2, rfl⟩ | ⟨a, ha, h2, rfl⟩)
    · exact ⟨by simp, by simp, Or.inl rfl⟩
    · refine ⟨zero_notMem_Icc ha, ?_, Or.inr ⟨a, ha, Or.inl rfl⟩⟩
      have := sum_E1 a ha
      omega
    · refine ⟨zero_notMem_Icc (by omega), ?_, Or.inr ⟨a, ha, Or.inr rfl⟩⟩
      have := sum_E2 a
      omega

