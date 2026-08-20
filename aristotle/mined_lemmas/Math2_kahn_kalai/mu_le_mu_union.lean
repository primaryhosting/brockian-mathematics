/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

lemma mu_le_mu_union {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {F : Finset (Finset α)} (hF : IsUp F) : mu a F ≤ mu (a + b - a * b) F := by
  classical
  have key := union_wt (α := α) a b (fun C => if C ∈ F then (1:ℝ) else 0)
  have hle : ∑ A : Finset α, ∑ B : Finset α,
      wt a A * wt b B * (if A ∈ F then (1:ℝ) else 0)
      ≤ ∑ A : Finset α, ∑ B : Finset α,
      wt a A * wt b B * (if A ∪ B ∈ F then (1:ℝ) else 0) := by
    refine Finset.sum_le_sum ?_
    intro A _
    refine Finset.sum_le_sum ?_
    intro B _
    have hw : 0 ≤ wt a A * wt b B :=
      mul_nonneg (wt_nonneg ha0 ha1 A) (wt_nonneg hb0 hb1 B)
    have : (if A ∈ F then (1:ℝ) else 0) ≤ (if A ∪ B ∈ F then (1:ℝ) else 0) := by
      by_cases hA : A ∈ F
      · have : A ∪ B ∈ F := hF A hA _ Finset.subset_union_left
        simp [hA, this]
      · simp [hA]
        positivity
    exact mul_le_mul_of_nonneg_left this hw
  have hsplit : ∑ A : Finset α, ∑ B : Finset α,
      wt a A * wt b B * (if A ∈ F then (1:ℝ) else 0) = mu a F := by
    rw [mu_eq_sum_ite]
    refine Finset.sum_congr rfl ?_
    intro A _
    have : ∀ B : Finset α, wt a A * wt b B * (if A ∈ F then (1:ℝ) else 0)
        = wt b B * (wt a A * (if A ∈ F then (1:ℝ) else 0)) := by
      intro B; ring
    simp only [this, ← Finset.sum_mul, sum_wt, one_mul]
    by_cases h : A ∈ F <;> simp [h]
  rw [hsplit] at hle
  rw [key] at hle
  calc mu a F ≤ ∑ C : Finset α, wt (a + b - a * b) C * (if C ∈ F then (1:ℝ) else 0) := hle
    _ = mu (a + b - a * b) F := by
        rw [mu_eq_sum_ite]
        exact Finset.sum_congr rfl (fun C _ => by by_cases h : C ∈ F <;> simp [h])

/-- Monotonicity of `mu` in the density. -/
