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

lemma mono_indep (c : Finset (Fin n) → ℝ)
    (h : ∀ x : Q n, ∑ T : Finset (Fin n), c T * mono T x = 0) : ∀ T, c T = 0 := by
  intro T
  induction T using Finset.strongInductionOn with
  | _ T ih =>
    have h0 := h (indic T)
    have hsum : ∑ T' : Finset (Fin n), c T' * mono T' (indic T) = ∑ T' ∈ T.powerset, c T' := by
      simp only [mono_indic, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext T'
      simp [Finset.mem_powerset]
    rw [hsum] at h0
    have hmemT : T ∈ T.powerset := Finset.mem_powerset_self T
    rw [← Finset.add_sum_erase _ _ hmemT] at h0
    have hzero : ∑ T' ∈ (T.powerset).erase T, c T' = 0 := by
      refine Finset.sum_eq_zero (fun T' hT' => ?_)
      have hne : T' ≠ T := (Finset.mem_erase.1 hT').1
      have hsub : T' ⊆ T := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hT')
      exact ih T' (lt_of_le_of_ne hsub hne)
    rw [hzero, add_zero] at h0
    exact h0

/-- Every real-valued function on the hypercube is a multilinear polynomial. -/
