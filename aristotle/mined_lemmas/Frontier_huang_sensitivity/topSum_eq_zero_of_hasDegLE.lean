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

lemma topSum_eq_zero_of_hasDegLE (hn : 1 ≤ n) {f : Q n → Bool} (h : HasDegLE f (n - 1)) :
    topSum f = 0 := by
  obtain ⟨p, hp, hrep⟩ := h
  have hstep : ∀ x : Q n, sgn x * (if f x then (1 : ℝ) else 0)
      = ∑ T : Finset (Fin n), p T * (sgn x * mono T x) := by
    intro x
    rw [hrep x, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T _ => by ring)
  unfold topSum
  rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  by_cases hT : T = univ
  · have hpT : p T = 0 := by
      refine hp T ?_
      rw [hT, Finset.card_univ, Fintype.card_fin]
      omega
    simp [hpT]
  · rw [← Finset.mul_sum, sum_sgn_mono T hT, mul_zero]

