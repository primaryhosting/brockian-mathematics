import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem exists_rotY_disjoint (D : Set E) (hD : D.Countable)
    (hax : ∀ d ∈ D, d 0 ≠ 0 ∨ d 2 ≠ 0) :
    ∃ t : ℝ, ∀ n : ℕ, 1 ≤ n → Disjoint ((RY t ^ n) • D) D := by
  classical
  -- for fixed data, the set of bad angles is countable
  have key : ∀ (m : ℕ) (d d' : E), d ∈ D → d' ∈ D →
      {t : ℝ | (RY t ^ (m + 1)) • d = d'}.Countable := by
    intro m d d' _ hd'
    rcases eq_empty_or_nonempty {t : ℝ | (RY t ^ (m + 1)) • d = d'} with h | ⟨t₀, ht₀⟩
    · rw [h]; exact countable_empty
    · refine Set.Countable.mono (s₂ := range fun k : ℤ => t₀ + k * (2 * Real.pi) / (m + 1)) ?_
        (countable_range _)
      intro t ht
      simp only [mem_setOf_eq] at ht ht₀
      rw [RY_pow] at ht ht₀
      -- `d'` is fixed by the rotation by the difference of the angles
      have hfix : RY ((m + 1 : ℕ) * t - (m + 1 : ℕ) * t₀) • d' = d' := by
        have : RY ((m + 1 : ℕ) * t - (m + 1 : ℕ) * t₀) • (RY ((m + 1 : ℕ) * t₀) • d) =
            RY ((m + 1 : ℕ) * t) • d := by
          rw [← SemigroupAction.mul_smul, ← RY_add]
          congr 2
          ring
        rw [ht₀] at this
        rw [this, ht]
      have hcos := cos_eq_one_of_fixed hfix (hax d' hd')
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
      refine ⟨k, ?_⟩
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      have : ((m : ℝ) + 1) * t - ((m : ℝ) + 1) * t₀ = k * (2 * Real.pi) := by
        push_cast at hk
        linarith [hk]
      field_simp
      linarith [this]
  set B : Set ℝ := ⋃ m : ℕ, ⋃ d ∈ D, ⋃ d' ∈ D, {t : ℝ | (RY t ^ (m + 1)) • d = d'} with hB
  have hBc : B.Countable := by
    refine countable_iUnion fun m => ?_
    refine hD.biUnion fun d hd => ?_
    exact hD.biUnion fun d' hd' => key m d d' hd hd'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ B := by
    by_contra hc
    push_neg at hc
    exact Cardinal.not_countable_real (by rwa [Set.eq_univ_iff_forall.mpr hc] at hBc)
  refine ⟨t, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ hx'
  exact ht (by
    rw [hB]
    refine mem_iUnion.2 ⟨m, ?_⟩
    refine mem_iUnion₂.2 ⟨d, hd, ?_⟩
    exact mem_iUnion₂.2 ⟨(RY t ^ (m + 1)) • d, hx', rfl⟩)

end BT

