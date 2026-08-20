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

lemma hL_hL (v : Q n → ℝ) : hL n (hL n v) = (n : ℝ) • v := by
  funext x
  set F : Fin n → Fin n → ℝ :=
    fun i j => eps x i * (eps (flipAt x i) j * v (flipAt (flipAt x i) j)) with hFdef
  set H : Fin n → Fin n → ℝ := fun i j => if j = i then 0 else F i j with hHdef
  have hFdiag : ∀ i, F i i = v x := by
    intro i
    have : eps (flipAt x i) i = eps x i := eps_flipAt_self x i
    rw [hFdef]
    simp only [this, flipAt_flipAt]
    rw [← mul_assoc, eps_mul_self, one_mul]
  have hHanti : ∀ i j, H j i = - H i j := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · simp [hHdef]
    · have h1 : H i j = F i j := by simp [hHdef, Ne.symm hij]
      have h2 : H j i = F j i := by simp [hHdef, hij]
      rw [h1, h2, hFdef]
      simp only
      rw [flipAt_comm x j i, ← mul_assoc, ← mul_assoc, eps_anticomm x hij]
      ring
  have hHzero : ∑ i : Fin n, ∑ j : Fin n, H i j = 0 := by
    have h1 : ∑ i : Fin n, ∑ j : Fin n, H i j = ∑ i : Fin n, ∑ j : Fin n, H j i :=
      Finset.sum_comm
    have h2 : ∑ i : Fin n, ∑ j : Fin n, H j i = - ∑ i : Fin n, ∑ j : Fin n, H i j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => hHanti i j)
    have := h1.trans h2
    linarith
  have hsplit : ∀ i : Fin n, ∑ j : Fin n, F i j = F i i + ∑ j : Fin n, H i j := by
    intro i
    have : ∑ j : Fin n, H i j = (∑ j : Fin n, F i j) - F i i := by
      have : ∀ j : Fin n, H i j = F i j - (if j = i then F i j else 0) := by
        intro j; by_cases h : j = i <;> simp [hHdef, h]
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' univ i (fun j => F i j)]
      simp
    rw [this]; ring
  have hgoal : hL n (hL n v) x = ∑ i : Fin n, ∑ j : Fin n, F i j := by
    simp only [hL_apply, Finset.mul_sum, hFdef]
  rw [hgoal, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun i _ => hFdiag i), hHzero]
  simp [mul_comm]

/-- Conjugation by the global sign flips the sign of the operator. -/
