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

theorem sum_bijs_univ (M : ι → ι → R) :
    ∑ f ∈ bijs Finset.univ.toList Finset.univ, (Finset.univ.toList.map (fun r => M r (f r))).prod
      = ∑ σ : Equiv.Perm ι, ∏ i, M i (σ i) := by
  refine (Finset.sum_nbij' (i := fun (σ : Equiv.Perm ι) => (⇑σ : ι → ι))
      (j := fun f => if h : Function.Bijective f then Equiv.ofBijective f h else 1)
      ?_ ?_ ?_ ?_ ?_).symm
  · intro σ _
    refine mem_bijs.mpr ⟨?_, ?_, ?_⟩
    · intro x hx
      exact absurd (Finset.mem_toList.mpr (Finset.mem_univ x)) hx
    · intro x _ y _ hxy
      exact σ.injective hxy
    · intro x _
      exact Finset.mem_univ _
  · intro f _
    exact Finset.mem_univ _
  · intro σ _
    dsimp only
    rw [dif_pos σ.bijective]
    exact Equiv.ext fun x => rfl
  · intro f hf
    have hinj : Function.Injective f := by
      intro x y hxy
      exact (mem_bijs.mp hf).2.1 x (Finset.mem_toList.mpr (Finset.mem_univ x)) y
        (Finset.mem_toList.mpr (Finset.mem_univ y)) hxy
    dsimp only
    rw [dif_pos (Finite.injective_iff_bijective.mp hinj)]
    rfl
  · intro σ _
    exact (Finset.prod_map_toList Finset.univ _).symm

/-- `pm` computes the permanent. -/
