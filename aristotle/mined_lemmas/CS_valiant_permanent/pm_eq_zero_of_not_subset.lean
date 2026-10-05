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

theorem pm_eq_zero_of_not_subset (M : ι → ι → R) (S : Finset ι) (l : List ι) (C : Finset ι)
    (hsupp : ∀ r ∈ l, ∀ c, c ∉ S → M r c = 0) (hC : ¬ C ⊆ S) : pm M l C = 0 := by
  obtain ⟨c₀, hc₀C, hc₀S⟩ := Finset.not_subset.mp hC
  exact pm_eq_zero_of_unreachable M c₀ l C hc₀C fun r hr => hsupp r hr c₀ hc₀S

/-- `pm` does not depend on the order in which the rows are listed. -/
