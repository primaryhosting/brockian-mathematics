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

theorem pm_peel_col (M : ι → ι → R) (l : List ι) (C : Finset ι) (r c : ι)
    (hr : r ∈ l) (hc : c ∈ C) (huniq : ∀ r' ∈ l, r' ≠ r → M r' c = 0) :
    pm M l C = M r c * pm M (l.erase r) (C.erase c) := by
  rw [pm_of_perm M (List.perm_cons_erase hr), pm_cons]
  rw [Finset.sum_eq_single c]
  · intro c' _ hc'
    rw [pm_eq_zero_of_unreachable M c _ _ (Finset.mem_erase.mpr ⟨hc', hc⟩)
      (fun r' hr' => huniq r' (List.mem_of_mem_erase hr') (List.ne_of_mem_erase hr')), mul_zero]
  · intro h
    exact absurd hc h

/-- Two groups of rows with disjoint column supports contribute independently. -/
