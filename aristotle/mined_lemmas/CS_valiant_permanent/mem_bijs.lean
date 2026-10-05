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

theorem mem_bijs {l : List ι} {C : Finset ι} {f : ι → ι} :
    f ∈ bijs l C ↔ (∀ x, x ∉ l → f x = x) ∧
      (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) ∧ (∀ x ∈ l, f x ∈ C) := by
  simp [bijs]

