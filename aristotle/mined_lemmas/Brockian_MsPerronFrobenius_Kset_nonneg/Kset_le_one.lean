import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma Kset_le_one {δ : ℝ} (hδ : 0 ≤ δ) {x : Fin n → ℝ} (hx : x ∈ Kset n δ) (i : Fin n) :
    x i ≤ 1 := by
  have hnonneg : ∀ j, 0 ≤ x j := fun j => le_trans hδ (hx.1 j)
  calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    _ = 1 := hx.2

