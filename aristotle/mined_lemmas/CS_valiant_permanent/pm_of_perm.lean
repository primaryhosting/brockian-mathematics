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

theorem pm_of_perm (M : ι → ι → R) {l l' : List ι} (h : l.Perm l') (C : Finset ι) :
    pm M l C = pm M l' C := by
  induction h generalizing C with
  | nil => rfl
  | cons x _ ih => simp only [pm_cons]; exact Finset.sum_congr rfl fun c _ => by rw [ih]
  | swap x y l => exact pm_swap M y x l C
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- If a column `c` can only be covered by the row `r`, peel both off. -/
