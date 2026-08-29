/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Weaver's discrepancy-theoretic form `KS₂` of the Kadison–Singer problem, in dimension `d`,
with smallness parameter `ε` and discrepancy constant `C`.

Given finitely many vectors `v i` in `ℂ^d` which form a Parseval frame
(`∑ i, |⟪v i, x⟫|² = ‖x‖²` for all `x`, i.e. `∑ i, v i v i* = I`) and each of which is small
(`‖v i‖² ≤ ε`), the index set can be split into two halves each of which is a frame with
upper bound `C` (i.e. the operator norm of each of the two partial sums `∑ v i v i*` is at
most `C`).

The Marcus–Spielman–Srivastava theorem states that this holds for every `d` and every `ε > 0`
with `C = (1/√2 + √ε)²`. -/

theorem exists_balanced_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (h0 : ∀ i ∈ s, 0 ≤ a i) (hε : ∀ i ∈ s, a i ≤ ε) :
    ∃ T ⊆ s, |(∑ i ∈ T, a i) - ∑ i ∈ s \ T, a i| ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simpa using hε0⟩
  | insert j s hj ih =>
      obtain ⟨T, hTs, hT⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hε i (Finset.mem_insert_of_mem hi))
      have hja : 0 ≤ a j := h0 j (Finset.mem_insert_self _ _)
      have hjε : a j ≤ ε := hε j (Finset.mem_insert_self _ _)
      have hjT : j ∉ T := fun h => hj (hTs h)
      have habs := abs_le.mp hT
      by_cases hle : (∑ i ∈ T, a i) ≤ ∑ i ∈ s \ T, a i
      · refine ⟨insert j T, Finset.insert_subset_insert _ hTs, ?_⟩
        have h1 : ∑ i ∈ insert j T, a i = a j + ∑ i ∈ T, a i := Finset.sum_insert hjT
        have h2 : (insert j s) \ (insert j T) = s \ T := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
          constructor
          · rintro ⟨hx | hx, hx2, hx3⟩
            · exact absurd hx hx2
            · exact ⟨hx, hx3⟩
          · rintro ⟨hx, hx2⟩
            exact ⟨Or.inr hx, by rintro rfl; exact hj hx, hx2⟩
        rw [h1, h2, abs_le]
        constructor <;> linarith [habs.1, habs.2]
      · push_neg at hle
        refine ⟨T, hTs.trans (Finset.subset_insert _ _), ?_⟩
        have h2 : (insert j s) \ T = insert j (s \ T) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hx2⟩
            · exact Or.inl hx
            · exact Or.inr ⟨hx, hx2⟩
          · rintro (rfl | ⟨hx, hx2⟩)
            · exact ⟨Or.inl rfl, hjT⟩
            · exact ⟨Or.inr hx, hx2⟩
        have hjsT : j ∉ s \ T := fun h => hj (Finset.mem_sdiff.mp h).1
        rw [h2, Finset.sum_insert hjsT, abs_le]
        constructor <;> linarith [habs.1, habs.2]

/-- Each part of a balanced split carries at most half the total plus `ε/2`. -/
