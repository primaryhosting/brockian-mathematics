/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma exists_Icc_squeeze (a b : ℝ) : ∃ α β : ℝ, 0 ≤ α ∧ α ≤ β ∧ β ≤ Real.pi ∧
    Ioo a b ∩ Icc 0 Real.pi ⊆ Icc α β ∧ Icc α β ⊆ (Ioo a b ∩ Icc 0 Real.pi) ∪ {α, β} := by
  have hpi : (0:ℝ) ≤ Real.pi := Real.pi_nonneg
  refine ⟨min (max a 0) Real.pi, max (min b Real.pi) (min (max a 0) Real.pi), ?_, ?_, ?_, ?_, ?_⟩
  · exact le_min (le_max_right _ _) hpi
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (min_le_right _ _)
  · rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨min_le_of_left_le (max_le h1.le h3), le_max_of_le_left (le_min h2.le h4)⟩
  · rintro x ⟨h1, h2⟩
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    have hx0 : 0 ≤ x := le_trans (le_min (le_max_right _ _) hpi) h1
    have hxpi : x ≤ Real.pi := le_trans h2 (max_le (min_le_right _ _) (min_le_right _ _))
    by_cases hax : a < x
    · by_cases hxb : x < b
      · exact Or.inl ⟨⟨hax, hxb⟩, ⟨hx0, hxpi⟩⟩
      · push_neg at hxb
        rw [min_eq_left (le_trans hxb hxpi)] at h2 ⊢
        exact Or.inr (Or.inr (le_antisymm h2 (max_le hxb h1)))
    · push_neg at hax
      refine Or.inr (Or.inl (le_antisymm ?_ h1))
      rcases le_total a 0 with ha | ha
      · rw [max_eq_right ha]; exact le_min (hax.trans ha) hxpi
      · rw [max_eq_left ha]; exact le_min hax hxpi

/-- Under the counting form of the Sato–Tate law, the proportion of primes whose angle equals a
given value tends to zero. -/
