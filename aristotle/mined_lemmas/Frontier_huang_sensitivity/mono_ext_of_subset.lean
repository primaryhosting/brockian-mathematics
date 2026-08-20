import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

lemma mono_ext_of_subset {T' : Finset (Fin n)} (hT' : T' ⊆ T) (y : Q d) :
    mono T' (ext T hd y) = mono (univ.filter (fun j : Fin d => emb T hd j ∈ T')) y := by
  have hTU : T' = (univ.filter (fun j : Fin d => emb T hd j ∈ T')).image (emb T hd) :=
    (preimage_image_emb T hd hT').symm
  calc mono T' (ext T hd y)
      = ∏ i ∈ (univ.filter (fun j : Fin d => emb T hd j ∈ T')).image (emb T hd),
          (if ext T hd y i then (1 : ℝ) else 0) := by rw [mono, ← hTU]
    _ = ∏ j ∈ univ.filter (fun j : Fin d => emb T hd j ∈ T'),
          (if ext T hd y (emb T hd j) then (1 : ℝ) else 0) :=
        Finset.prod_image (fun a _ b _ h => emb_injective T hd h)
    _ = mono (univ.filter (fun j : Fin d => emb T hd j ∈ T')) y := by
        exact Finset.prod_congr rfl (fun j _ => by rw [ext_emb])

