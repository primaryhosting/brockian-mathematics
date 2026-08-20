import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem isPoly_support {γ : Type} : ∀ {F : (γ → ℕ) → ℤ}, IsPoly F →
    ∃ s : Finset γ, ∀ v w : γ → ℕ, (∀ i ∈ s, v i = w i) → F v = F w := by
  classical
  intro F hF
  induction hF with
  | proj i =>
      exact ⟨{i}, fun v w h => by show ((v i : ℤ)) = (w i : ℤ); rw [h i (by simp)]⟩
  | const n => exact ⟨∅, fun v w _ => rfl⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨s1, h1⟩ := ih1; obtain ⟨s2, h2⟩ := ih2
      refine ⟨s1 ∪ s2, fun v w h => ?_⟩
      show _ - _ = _ - _
      rw [h1 v w (fun i hi => h i (by simp [hi])), h2 v w (fun i hi => h i (by simp [hi]))]
  | mul _ _ ih1 ih2 =>
      obtain ⟨s1, h1⟩ := ih1; obtain ⟨s2, h2⟩ := ih2
      refine ⟨s1 ∪ s2, fun v w h => ?_⟩
      show _ * _ = _ * _
      rw [h1 v w (fun i hi => h i (by simp [hi])), h2 v w (fun i hi => h i (by simp [hi]))]

/-- Every Diophantine set can be described using only finitely many witness variables. -/
