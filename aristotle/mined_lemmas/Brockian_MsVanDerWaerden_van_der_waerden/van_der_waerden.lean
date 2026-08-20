import Mathlib
namespace Brockian.MsVanDerWaerden

open Combinatorics Finset

/-- The set of "moving" coordinates of a combinatorial line. -/

theorem van_der_waerden (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    ∃ N : ℕ, ∀ c : ℕ → Fin r, ∃ a d : ℕ, 0 < d ∧
      (∀ i, i < k → a + i * d ≤ N) ∧
      (∀ i j, i < k → j < k → c (a + i * d) = c (a + j * d)) := by
  obtain ⟨ι, hfin, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨Fintype.card ι * k, fun c => ?_⟩
  obtain ⟨l, col, hl⟩ := hι (fun v => c (∑ i, ((v i : ℕ))))
  refine ⟨lineConst l, (movingSet l).card, ?_, ?_, ?_⟩
  · rw [Finset.card_pos]
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [movingSet, hi]⟩
  · intro i hi
    rw [← line_sum_eq l ⟨i, hi⟩]
    exact sum_coords_le _
  · intro i j hi hj
    rw [← line_sum_eq l ⟨i, hi⟩, ← line_sum_eq l ⟨j, hj⟩]
    exact (hl ⟨i, hi⟩).trans (hl ⟨j, hj⟩).symm

end Brockian.MsVanDerWaerden

