/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/

theorem split_semiDecisive {F : (V → Ranking) → Ranking} (hIIA : IIA F) {S₁ S₂ : List V}
    (hdisj : ∀ v, v ∈ S₁ → v ∉ S₂) (hdec : Decisive F (S₁ ++ S₂) 0 1) :
    (∃ x y : Fin 3, x ≠ y ∧ SemiDecisive F S₁ x y) ∨
      (∃ x y : Fin 3, x ≠ y ∧ SemiDecisive F S₂ x y) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- `S₁` votes `0 ≻ 1 ≻ 2`, `S₂` votes `2 ≻ 0 ≻ 1`, everybody else votes `1 ≻ 2 ≻ 0`
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun v =>
      if v ∈ S₁ then mkRank 0 1 2 h01 h02 h12
      else if v ∈ S₂ then mkRank 2 0 1 (Ne.symm h02) (Ne.symm h12) h01
      else mkRank 1 2 0 h12 (Ne.symm h01) (Ne.symm h02) := ⟨_, rfl⟩
  have h₁ : ∀ v, v ∈ S₁ → p v = mkRank 0 1 2 h01 h02 h12 := by
    intro v hv; rw [hp]; simp [hv]
  have h₂ : ∀ v, v ∉ S₁ → v ∈ S₂ → p v = mkRank 2 0 1 (Ne.symm h02) (Ne.symm h12) h01 := by
    intro v hv1 hv2; rw [hp]; simp [hv1, hv2]
  have h₃ : ∀ v, v ∉ S₁ → v ∉ S₂ → p v = mkRank 1 2 0 h12 (Ne.symm h01) (Ne.symm h02) := by
    intro v hv1 hv2; rw [hp]; simp [hv1, hv2]
  have hFab : prefers (F p) 0 1 := by
    refine hdec p ?_
    intro v hv
    rcases List.mem_append.mp hv with hv1 | hv2
    · simp [prefers, h₁ v hv1]
    · by_cases hv1 : v ∈ S₁
      · simp [prefers, h₁ v hv1]
      · simp [prefers, h₂ v hv1 hv2]
  by_cases hcase : prefers (F p) 0 2
  · -- `S₁` is semi-decisive for `(0, 2)`
    left
    refine ⟨0, 2, h02, ?_⟩
    intro q hq1 hq2
    have hkey : ∀ v, prefers (p v) 0 2 ↔ prefers (q v) 0 2 := by
      intro v
      by_cases hv : v ∈ S₁
      · exact iff_of_true (by simp [prefers, h₁ v hv]) (hq1 v hv)
      · have hq : ¬ prefers (q v) 0 2 := prefers_asymm (hq2 v hv)
        by_cases hv2 : v ∈ S₂
        · exact iff_of_false (by simp [prefers, h₂ v hv hv2]) hq
        · exact iff_of_false (by simp [prefers, h₃ v hv hv2]) hq
    exact (hIIA p q 0 2 hkey).mp hcase
  · -- `S₂` is semi-decisive for `(2, 1)`
    right
    refine ⟨2, 1, Ne.symm h12, ?_⟩
    intro q hq1 hq2
    have h20 : prefers (F p) 2 0 := prefers_total h02 hcase
    have h21 : prefers (F p) 2 1 := prefers_trans h20 hFab
    have hkey : ∀ v, prefers (p v) 2 1 ↔ prefers (q v) 2 1 := by
      intro v
      by_cases hv2 : v ∈ S₂
      · have hv1 : v ∉ S₁ := fun h => hdisj v h hv2
        exact iff_of_true (by simp [prefers, h₂ v hv1 hv2]) (hq1 v hv2)
      · have hq : ¬ prefers (q v) 2 1 := prefers_asymm (hq2 v hv2)
        by_cases hv1 : v ∈ S₁
        · exact iff_of_false (by simp [prefers, h₁ v hv1]) hq
        · exact iff_of_false (by simp [prefers, h₃ v hv1 hv2]) hq
    exact (hIIA p q 2 1 hkey).mp h21

/-- The empty coalition is not decisive. -/
