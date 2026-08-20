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

lemma hasDegLE_of_topSum_eq_zero (hn : 1 ≤ n) (f : Q n → Bool) (h : topSum f = 0) :
    HasDegLE f (n - 1) := by
  obtain ⟨p, hp⟩ := exists_multilinear_repr (fun x => if f x then (1 : ℝ) else 0)
  have huniv : p univ = 0 := by
    have hstep : ∀ x : Q n, sgn x * (if f x then (1 : ℝ) else 0)
        = ∑ T : Finset (Fin n), p T * (sgn x * mono T x) := by
      intro x
      rw [hp x, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun T _ => by ring)
    have hts : topSum f = p univ * sgn (fun _ : Fin n => true) := by
      unfold topSum
      rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
      rw [Finset.sum_eq_single (univ : Finset (Fin n))]
      · rw [← Finset.mul_sum, sum_sgn_mono_univ]
      · intro T _ hT
        rw [← Finset.mul_sum, sum_sgn_mono T hT, mul_zero]
      · intro hc
        exact absurd (Finset.mem_univ _) hc
    rw [h] at hts
    rcases mul_self_eq_one_iff.1 (sgn_mul_self (fun _ => true : Q n)) with h1 | h1 <;>
      rw [h1] at hts <;> linarith
  refine ⟨p, ?_, hp⟩
  intro T hT
  have hTu : T = univ := by
    refine Finset.eq_univ_of_card T ?_
    have hle := Finset.card_le_univ T
    rw [Fintype.card_fin] at hle ⊢
    omega
  rw [hTu, huniv]

/-- **Huang's sensitivity theorem** in the full-degree case: a Boolean function on `n ≥ 1`
variables whose multilinear representation has degree `n` (i.e. which is not represented by
any multilinear polynomial of degree at most `n - 1`) has sensitivity at least `√n`. -/
