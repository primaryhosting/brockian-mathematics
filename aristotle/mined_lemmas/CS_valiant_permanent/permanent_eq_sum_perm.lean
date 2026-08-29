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

theorem permanent_eq_sum_perm (M : Matrix ι ι R) :
    M.permanent = ∑ σ : Equiv.Perm ι, ∏ i, M i (σ i) := by
  rw [← Matrix.permanent_transpose]
  rfl

