import Mathlib
open Finset
namespace C6.P5

theorem prob_sum_one {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : ∀ i, p i ≤ 1 := by
  intro i
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
