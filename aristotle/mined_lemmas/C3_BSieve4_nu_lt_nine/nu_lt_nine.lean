import Mathlib
namespace C3.BSieve4

theorem nu_lt_nine (p : ℕ) (hp : p.Prime) :
    nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p < p := by
  by_cases h : p < 10
  · interval_cases p <;> simp_all (config := {decide := true})
  · push_neg at h
    calc nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p
        ≤ ({0,2,6,8,12,18,20,26,30} : Finset ℕ).card := Finset.card_image_le
      _ = 9 := by decide
      _ < p := by omega

