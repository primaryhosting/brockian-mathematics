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

lemma finrank_range_Cop_eq_finrank_range_Bop (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (Cop n)) = Module.finrank ℝ (LinearMap.range (Bop n)) := by
  have hcomp : Bop n = (Dlin n) ∘ₗ ((Cop n) ∘ₗ (Dlin n)) :=
    LinearMap.ext (fun v => (Dlin_Cop_Dlin v).symm)
  have hrange : LinearMap.range (Bop n) = Submodule.map (Dlin n) (LinearMap.range (Cop n)) := by
    rw [hcomp, LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top (Cop n)
        (LinearMap.range_eq_top.2 (Dlin_surjective (n := n)))]
  rw [hrange]
  exact (Submodule.equivMapOfInjective (Dlin n) Dlin_injective _).finrank_eq

