import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₅`, i.e. the Hückel matrix of
cyclopentadienyl (with `α = 0`, `β = 1`). -/
noncomputable def C5 : Matrix (Fin 5) (Fin 5) ℝ := (SimpleGraph.cycleGraph 5).adjMatrix ℝ

/-- Explicit description of the adjacency matrix of `C₅`. -/
lemma C5_eq : C5 = !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C5, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;> decide

lemma scalar_sub_C5 (t : ℝ) :
    (Matrix.scalar (Fin 5) t - C5)
      = !![t,-1,0,0,-1; -1,t,-1,0,0; 0,-1,t,-1,0; 0,0,-1,t,-1; -1,0,0,-1,t] := by
  rw [C5_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

/-- The characteristic polynomial of the adjacency matrix of `C₅`,
evaluated at `t`, is `t⁵ - 5t³ + 5t - 2`. -/
lemma charpoly_eval (t : ℝ) : C5.charpoly.eval t = t^5 - 5*t^3 + 5*t - 2 := by
  rw [Matrix.eval_charpoly, scalar_sub_C5]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num
  ring

lemma sqrt_five_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
  Real.mul_self_sqrt (by norm_num)

/-- The real roots of `t⁵ - 5t³ + 5t - 2`. -/
lemma quintic_root_iff (t : ℝ) :
    t^5 - 5*t^3 + 5*t - 2 = 0 ↔
      t = 2 ∨ t = (Real.sqrt 5 - 1)/2 ∨ t = -(1 + Real.sqrt 5)/2 := by
  have hfac : t^5 - 5*t^3 + 5*t - 2
      = (t - 2) * ((t - (Real.sqrt 5 - 1)/2) * (t + (1 + Real.sqrt 5)/2))^2 := by
    have h : (t - (Real.sqrt 5 - 1)/2) * (t + (1 + Real.sqrt 5)/2) = t^2 + t - 1 := by
      linear_combination (-1/4 : ℝ) * sqrt_five_sq
    rw [h]; ring
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (by linarith [sub_eq_zero.1 h])
    · have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inr (Or.inl (by linarith [sub_eq_zero.1 h'']))
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> ring

lemma mem_spectrum_iff (t : ℝ) :
    t ∈ spectrum ℝ C5 ↔ t = 2 ∨ t = (Real.sqrt 5 - 1)/2 ∨ t = -(1 + Real.sqrt 5)/2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, charpoly_eval,
    quintic_root_iff]

lemma cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  rw [show (2 * Real.pi / 5 : ℝ) = 2 * (Real.pi / 5) by ring, Real.cos_two_mul,
    Real.cos_pi_div_five]
  linear_combination (1/8 : ℝ) * sqrt_five_sq

lemma cos_four_pi_div_five : Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  rw [show (4 * Real.pi / 5 : ℝ) = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_five]
  ring

lemma cos_six_pi_div_five : Real.cos (6 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  rw [show (6 * Real.pi / 5 : ℝ) = Real.pi + Real.pi / 5 by ring, Real.cos_add,
    Real.cos_pi_div_five]
  simp
  ring

lemma cos_eight_pi_div_five : Real.cos (8 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  rw [show (8 * Real.pi / 5 : ℝ) = 2 * Real.pi - 2 * Real.pi / 5 by ring, Real.cos_sub,
    Real.cos_two_pi, Real.sin_two_pi, cos_two_pi_div_five]
  ring

/-- **Hückel theory for cyclopentadienyl.** The spectrum of the adjacency matrix of the
cycle graph `C₅` is exactly `{2 cos (2πk/5) : k = 0,…,4}`. -/
theorem huckel_C5 :
    spectrum ℝ ((SimpleGraph.cycleGraph 5).adjMatrix ℝ)
      = {μ : ℝ | ∃ k : Fin 5, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 5)} := by
  ext t
  rw [show (SimpleGraph.cycleGraph 5).adjMatrix ℝ = C5 from rfl, mem_spectrum_iff]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · refine ⟨1, ?_⟩
      rw [show (2 * Real.pi * ((1 : Fin 5) : ℕ) / 5 : ℝ) = 2 * Real.pi / 5 by norm_num,
        cos_two_pi_div_five]
      ring
    · refine ⟨2, ?_⟩
      rw [show (2 * Real.pi * ((2 : Fin 5) : ℕ) / 5 : ℝ) = 4 * Real.pi / 5 by norm_num; ring,
        cos_four_pi_div_five]
      ring
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; norm_num
    · right; left
      rw [show (2 * Real.pi * ((⟨1, by norm_num⟩ : Fin 5) : ℕ) / 5 : ℝ) = 2 * Real.pi / 5 by
          norm_num, cos_two_pi_div_five]
      ring
    · right; right
      rw [show (2 * Real.pi * ((⟨2, by norm_num⟩ : Fin 5) : ℕ) / 5 : ℝ) = 4 * Real.pi / 5 by
          norm_num; ring, cos_four_pi_div_five]
      ring
    · right; right
      rw [show (2 * Real.pi * ((⟨3, by norm_num⟩ : Fin 5) : ℕ) / 5 : ℝ) = 6 * Real.pi / 5 by
          norm_num; ring, cos_six_pi_div_five]
      ring
    · right; left
      rw [show (2 * Real.pi * ((⟨4, by norm_num⟩ : Fin 5) : ℕ) / 5 : ℝ) = 8 * Real.pi / 5 by
          norm_num; ring, cos_eight_pi_div_five]
      ring

end Chem

