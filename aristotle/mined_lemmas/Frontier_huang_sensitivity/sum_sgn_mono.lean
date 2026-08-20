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

lemma sum_sgn_mono (T : Finset (Fin n)) (hT : T ≠ univ) :
    ∑ x : Q n, sgn x * mono T x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
    by_contra hc
    push_neg at hc
    exact hT (Finset.eq_univ_iff_forall.2 hc)
  refine Finset.sum_ninvolution (fun x => flipAt x i) ?_ ?_ (fun _ => Finset.mem_univ _) ?_
  · intro x
    have hmono : mono T (flipAt x i) = mono T x := by
      unfold mono
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [flipAt_apply_of_ne _ hji]
    rw [hmono, sgn_flipAt]
    ring
  · intro x _
    exact flipAt_ne_self x i
  · intro x
    exact flipAt_flipAt x i

