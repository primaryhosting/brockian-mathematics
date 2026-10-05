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

theorem pm_swap (M : ι → ι → R) (a b : ι) (l : List ι) (C : Finset ι) :
    pm M (a :: b :: l) C = pm M (b :: a :: l) C := by
  simp only [pm_cons]
  rw [Finset.sum_comm' (t' := C) (s' := fun c₂ => C.erase c₂)
    (by
      intro c₁ c₂
      simp only [Finset.mem_erase]
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨⟨fun h => h₂ h.symm, h₁⟩, h₃⟩
      · rintro ⟨⟨h₁, h₂⟩, h₃⟩
        exact ⟨h₂, fun h => h₁ h.symm, h₃⟩)]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Finset.erase_right_comm]
  ring

