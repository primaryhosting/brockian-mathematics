/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma two_mul_sum_pent1 {c : ℕ} (hc : 1 ≤ c) :
    2 * (∑ i ∈ Finset.Icc c (2 * c - 1), i) = c * (3 * c - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
  have h1 : 2 * (e + 1) - 1 = (e + 1) + e := by omega
  have h2 : 3 * (e + 1) - 1 = 3 * e + 2 := by omega
  rw [h1, h2, two_mul_sum_Icc_add]
  ring

