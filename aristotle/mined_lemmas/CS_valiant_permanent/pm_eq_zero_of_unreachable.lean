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

theorem pm_eq_zero_of_unreachable (M : ι → ι → R) (c₀ : ι) :
    ∀ (l : List ι) (C : Finset ι), c₀ ∈ C → (∀ r ∈ l, M r c₀ = 0) → pm M l C = 0 := by
  intro l
  induction l with
  | nil =>
      intro C hc₀ _
      rw [pm_nil, if_neg]
      rintro rfl
      exact absurd hc₀ (Finset.notMem_empty _)
  | cons r rs ih =>
      intro C hc₀ hz
      rw [pm_cons]
      refine Finset.sum_eq_zero fun c hc => ?_
      by_cases hcc : c = c₀
      · subst hcc
        rw [hz r List.mem_cons_self, zero_mul]
      · rw [ih _ (Finset.mem_erase.mpr ⟨fun h => hcc h.symm, hc₀⟩)
            (fun r' hr' => hz r' (List.mem_cons_of_mem _ hr')), mul_zero]

/-- If all rows of `l` are supported inside `S` while `C` sticks out of `S`, nothing is counted. -/
