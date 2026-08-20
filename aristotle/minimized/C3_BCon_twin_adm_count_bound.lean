import Mathlib
namespace C3.BCon

theorem twin_adm_count_bound (n : ℕ) [NeZero n] (hn : 0 < n) :
    (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card ≤ n := by
  calc (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := by simp [ZMod.card]

/-- Translation by `3` has no fixed point in `ZMod n` when `n > 3`. -/
