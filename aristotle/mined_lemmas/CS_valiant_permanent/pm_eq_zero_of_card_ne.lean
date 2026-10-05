import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

/-! ## A recursive description of the permanent

`pm M l C` is the weighted count of bijections from the rows listed in `l` onto the
column set `C`, where the weight of a bijection is the product of the corresponding
matrix entries.  It is a convenient recursive handle on the permanent. -/

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- Weighted count of the bijections from the rows in the list `l` onto the columns in `C`. -/

theorem pm_eq_zero_of_card_ne (M : ι → ι → R) :
    ∀ (l : List ι) (C : Finset ι), C.card ≠ l.length → pm M l C = 0 := by
  intro l
  induction l with
  | nil => intro C h; simp only [pm_nil, List.length_nil] at *; rw [if_neg]; intro hC; exact h (by simp [hC])
  | cons r rs ih =>
      intro C h
      rw [pm_cons]
      refine Finset.sum_eq_zero fun c hc => ?_
      have hpos : 0 < C.card := Finset.card_pos.mpr ⟨c, hc⟩
      have hne : (C.erase c).card ≠ rs.length := by
        rw [Finset.card_erase_of_mem hc]
        simp only [List.length_cons] at h
        omega
      rw [ih _ hne, mul_zero]

/-- Splitting the list of rows into two halves: the columns get distributed. -/
