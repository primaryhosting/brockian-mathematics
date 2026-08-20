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

lemma topSum_restrict (f : Q n → Bool) :
    topSum (restrict T hd f) = coeff f T * sgn (fun _ : Fin d => true) := by
  have hstep : ∀ y : Q d, sgn y * (if restrict T hd f y then (1 : ℝ) else 0)
      = ∑ T' : Finset (Fin n), coeff f T' * (sgn y * mono T' (ext T hd y)) := by
    intro y
    unfold restrict
    rw [coeff_spec f (ext T hd y), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T' _ => by ring)
  unfold topSum
  rw [Finset.sum_congr rfl (fun y _ => hstep y), Finset.sum_comm]
  rw [Finset.sum_eq_single T]
  · rw [← Finset.mul_sum]
    congr 1
    have hUT : (univ.filter (fun j : Fin d => emb T hd j ∈ T)) = univ := by
      ext j
      simp [emb_mem T hd j]
    have : ∀ y : Q d, sgn y * mono T (ext T hd y) = sgn y * mono (univ : Finset (Fin d)) y := by
      intro y
      rw [mono_ext_of_subset T hd (subset_refl T) y, hUT]
    rw [Finset.sum_congr rfl (fun y _ => this y), sum_sgn_mono_univ]
  · intro T' _ hT'
    by_cases hsub : T' ⊆ T
    · have hU : (univ.filter (fun j : Fin d => emb T hd j ∈ T')) ≠ univ := by
        intro hU
        refine hT' (le_antisymm hsub ?_)
        intro i hi
        obtain ⟨j, rfl⟩ := exists_emb_eq T hd hi
        have : j ∈ univ.filter (fun j : Fin d => emb T hd j ∈ T') := by rw [hU]; exact mem_univ j
        exact (Finset.mem_filter.1 this).2
      have : ∀ y : Q d, sgn y * mono T' (ext T hd y)
          = sgn y * mono (univ.filter (fun j : Fin d => emb T hd j ∈ T')) y :=
        fun y => by rw [mono_ext_of_subset T hd hsub y]
      rw [← Finset.mul_sum, Finset.sum_congr rfl (fun y _ => this y),
        sum_sgn_mono _ hU, mul_zero]
    · have : ∀ y : Q d, sgn y * mono T' (ext T hd y) = 0 :=
        fun y => by rw [mono_ext_of_not_subset T hd hsub y, mul_zero]
      rw [← Finset.mul_sum, Finset.sum_congr rfl (fun y _ => this y), Finset.sum_const_zero,
        mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

end Restriction

section Main

variable {n : ℕ}

/-- **Huang's sensitivity theorem**: the sensitivity of a Boolean function is at least the
square root of its degree. -/
