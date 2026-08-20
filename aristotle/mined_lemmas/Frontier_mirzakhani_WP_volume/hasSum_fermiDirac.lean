import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

theorem hasSum_fermiDirac {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => etaCoeff n * (rexp (-(n : ℝ) * t) : ℝ)) (fermiDirac t) := by
  set r : ℂ := -(rexp (-t) : ℝ) with hr
  have hrn : ‖r‖ < 1 := by
    rw [hr]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_norm_lt_one hrn
  have hg2 := (hg.neg).add (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
  have hval : -(1 - r)⁻¹ + 1 = fermiDirac t := by
    rw [hr, fermiDirac]
    have h1 : (rexp t) ≠ 0 := (Real.exp_pos t).ne'
    have h2 : (1 : ℝ) + rexp t ≠ 0 := by positivity
    have h3 : Real.exp (-t) = (rexp t)⁻¹ := by rw [Real.exp_neg]
    rw [h3]
    push_cast
    have h5 : (1 : ℂ) + Complex.exp (t : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_exp]
      exact_mod_cast Complex.ofReal_ne_zero.mpr h2
    have h4 : Complex.exp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    rw [show Complex.exp (t : ℂ) - -1 = 1 + Complex.exp (t : ℂ) from by ring]
    field_simp
    ring
  rw [hval] at hg2
  refine hg2.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · subst hn; simp [etaCoeff]
  · have hrp : r ^ n = (-1) ^ n * ((rexp (-(n : ℝ) * t) : ℝ) : ℂ) := by
      rw [hr, neg_pow]
      congr 1
      rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
      norm_num
    rw [hrp]
    simp only [etaCoeff, if_neg hn]
    rw [pow_succ]
    ring

