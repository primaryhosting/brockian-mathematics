import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem delta_mem_span {ζ : F} (hζ1 : ζ ≠ 1) (y : Cube n) :
    (delta y : Cube n → F) ∈ Submodule.span F (Set.range (UU ζ)) := by
  classical
  have hz : ζ - 1 ≠ 0 := sub_ne_zero_of_ne hζ1
  set a : Fin n → F := fun i => if y i then (ζ - 1)⁻¹ else -(ζ - 1)⁻¹ with ha
  set b : Fin n → F := fun i => if y i then -(ζ - 1)⁻¹ else ζ * (ζ - 1)⁻¹ with hb
  have hfac : (delta y : Cube n → F)
      = ∏ i, ((a i) • uu ζ i + (fun _ : Cube n => b i)) := by
    funext x
    simp only [delta, Finset.prod_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases hy : y i <;> cases hx : x i <;>
      simp [ha, hb, hy, hx, uu, bitv] <;> field_simp <;> ring
  rw [hfac, Finset.prod_add]
  refine Submodule.sum_mem _ fun T _ => ?_
  have hval : (∏ i ∈ T, (a i) • uu ζ i) * (∏ i ∈ Finset.univ \ T, (fun _ : Cube n => b i))
      = ((∏ i ∈ T, a i) * (∏ i ∈ Finset.univ \ T, b i)) • UU ζ T := by
    funext x
    simp only [Finset.prod_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, UU]
    rw [Finset.prod_mul_distrib]
    simp [mul_comm, mul_assoc]
  rw [hval]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩)

