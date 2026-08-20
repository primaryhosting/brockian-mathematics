import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma exists_min_qb {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) :
    ∃ x₀ y₀ : ℤ, ¬(x₀ = 0 ∧ y₀ = 0) ∧
      ∀ x y : ℤ, ¬(x = 0 ∧ y = 0) → qb A B C x₀ y₀ ≤ qb A B C x y := by
  classical
  set S : Set ℕ := {k : ℕ | ∃ x y : ℤ, ¬(x = 0 ∧ y = 0) ∧ qb A B C x y = (k : ℤ)} with hS
  have hne : S.Nonempty := by
    refine ⟨(qb A B C 1 0).toNat, 1, 0, by simp, ?_⟩
    have : 0 < qb A B C 1 0 := qb_pos hA hD (by simp)
    omega
  obtain ⟨m, hmS, hmin⟩ := Nat.lt_wfRel.wf.has_min S hne
  obtain ⟨x₀, y₀, hne0, hval⟩ := hmS
  refine ⟨x₀, y₀, hne0, ?_⟩
  intro x y hxy
  have hpos : 0 < qb A B C x y := qb_pos hA hD hxy
  have hmem : (qb A B C x y).toNat ∈ S := ⟨x, y, hxy, by omega⟩
  have hle := hmin _ hmem
  simp only [Nat.lt_wfRel, not_lt] at hle
  omega

/-- The key reduction step: a vector realizing the minimum can be completed to a basis
in which the middle coefficient is small and the third coefficient is at least the minimum. -/
