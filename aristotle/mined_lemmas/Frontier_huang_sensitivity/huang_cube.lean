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

theorem huang_cube (hn : 1 ≤ n) (S : Finset (Q n)) (hS : 2 ^ (n - 1) < S.card) :
    ∃ x ∈ S, Real.sqrt n ≤ (univ.filter (fun i : Fin n => flipAt x i ∈ S)).card := by
  obtain ⟨v, hv0, hsupp, heig⟩ := exists_eigenvector hn S hS
  obtain ⟨x, hx⟩ : ∃ x : Q n, ∀ y : Q n, |v y| ≤ |v x| := Finite.exists_max _
  have hvx : 0 < |v x| := by
    obtain ⟨y, hy⟩ : ∃ y, v y ≠ 0 := by
      by_contra hc
      exact hv0 (funext (fun y => by simpa using not_exists.1 hc y))
    exact lt_of_lt_of_le (abs_pos.2 hy) (hx y)
  have hxS : x ∈ S := by
    by_contra hc
    rw [hsupp x hc] at hvx
    simp at hvx
  refine ⟨x, hxS, ?_⟩
  set F : Finset (Fin n) := univ.filter (fun i : Fin n => flipAt x i ∈ S) with hF
  have habs : ∀ i : Fin n, |eps x i| = 1 := by
    intro i
    rw [eps, sgnp, abs_pow, abs_neg, abs_one, one_pow]
  have key : Real.sqrt n * |v x| ≤ (F.card : ℝ) * |v x| := by
    have h1 : Real.sqrt n * |v x| = |∑ i : Fin n, eps x i * v (flipAt x i)| := by
      have : (∑ i : Fin n, eps x i * v (flipAt x i)) = Real.sqrt n * v x := by
        have := congrFun heig x
        simpa using this
      rw [this, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h2 : |∑ i : Fin n, eps x i * v (flipAt x i)| ≤ ∑ i : Fin n, |v (flipAt x i)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun i _ => by rw [abs_mul, habs i, one_mul])
    have h3 : (∑ i : Fin n, |v (flipAt x i)|) = ∑ i ∈ F, |v (flipAt x i)| := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro i _ hi
      have : flipAt x i ∉ S := by simpa [hF] using hi
      rw [hsupp _ this, abs_zero]
    have h4 : (∑ i ∈ F, |v (flipAt x i)|) ≤ (F.card : ℝ) * |v x| := by
      calc (∑ i ∈ F, |v (flipAt x i)|) ≤ ∑ _i ∈ F, |v x| :=
            Finset.sum_le_sum (fun i _ => hx _)
        _ = (F.card : ℝ) * |v x| := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    exact (h2.trans (le_of_eq h3)).trans h4
  exact le_of_mul_le_mul_right (by linarith) hvx

end Huang

section Sensitivity

variable {n : ℕ}

/-- The local sensitivity of `f` at `x`. -/
