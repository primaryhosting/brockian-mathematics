import Mathlib


theorem not_admissible_of_five_consecutive_mod_five :
    ¬ Admissible ({0, 1, 2, 3, 4} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 5 (by norm_num)
  revert hr
  revert r
  decide

