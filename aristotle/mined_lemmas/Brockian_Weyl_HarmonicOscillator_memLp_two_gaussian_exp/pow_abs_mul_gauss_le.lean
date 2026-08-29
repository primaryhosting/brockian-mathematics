/-
  RequestProject/ESA.lean

  Essential self-adjointness of the harmonic-oscillator core
  `harmonicOscillatorPMap` (the operator `-d²/dx² + x²` on the Schwartz core of
  `L²(ℝ)`).

  The argument is the classical deficiency-index one.  If `g` is in the domain of
  the adjoint with `T* g = z • g` and `Im z ≠ 0`, then pairing against the Hermite
  functions `hermiteFun n` (which lie in the Schwartz core and satisfy
  `H hermiteFun n = (2n+1) hermiteFun n`) forces `⟪g, hermiteFun n⟫ = 0` for every
  `n`, since `conj z ≠ 2n+1`.  The Hermite functions span every monomial
  `xⁿ e^{-x²/2}`, so all the moments of `x ↦ conj (g x) e^{-x²/2}` vanish, and the
  moment theorem gives `g = 0`.
-/
import RequestProject.Corpus
import RequestProject.Hermite
import RequestProject.Moments

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.Moments

/-! ### Integrability facts for an `L²` function against Gaussian weights -/


theorem pow_abs_mul_gauss_le (m : ℕ) (x : ℝ) :
    |x| ^ m * Real.exp (-(x ^ 2 / 2)) ≤ (m ! : ℝ) * 2 ^ m + 1 := by
  have hfac : (0 : ℝ) < (m ! : ℝ) := by positivity
  have hf1 : (1 : ℝ) ≤ (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rcases le_or_gt |x| 1 with h | h
  · have h1 : |x| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    have h2 : Real.exp (-(x ^ 2 / 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have h3 : (0 : ℝ) ≤ |x| ^ m := by positivity
    have h4 : (0 : ℝ) < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
    have h5 : (1 : ℝ) ≤ (m ! : ℝ) * 2 ^ m := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      nlinarith
    nlinarith
  · have hx0 : (0 : ℝ) < |x| := lt_trans zero_lt_one h
    have key : (x ^ 2 / 2) ^ m / (m ! : ℝ) ≤ Real.exp (x ^ 2 / 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) m
    have hxm : (x ^ 2 / 2) ^ m = |x| ^ (2 * m) / 2 ^ m := by
      rw [div_pow, pow_mul, sq_abs]
    have hexp : Real.exp (-(x ^ 2 / 2)) = (Real.exp (x ^ 2 / 2))⁻¹ := by rw [Real.exp_neg]
    have hpos : (0 : ℝ) < Real.exp (x ^ 2 / 2) := Real.exp_pos _
    have hlow : |x| ^ (2 * m) / (2 ^ m * (m ! : ℝ)) ≤ Real.exp (x ^ 2 / 2) := by
      rw [hxm] at key
      calc |x| ^ (2 * m) / (2 ^ m * (m ! : ℝ))
          = |x| ^ (2 * m) / 2 ^ m / (m ! : ℝ) := by rw [div_div]
        _ ≤ _ := key
    have hxpos : (0 : ℝ) < |x| ^ m := by positivity
    have h2m : |x| ^ (2 * m) = |x| ^ m * |x| ^ m := by rw [two_mul, pow_add]
    have hmain : |x| ^ m * Real.exp (-(x ^ 2 / 2)) ≤ (m ! : ℝ) * 2 ^ m := by
      rw [hexp, mul_inv_le_iff₀ hpos]
      calc |x| ^ m ≤ (m ! : ℝ) * 2 ^ m * (|x| ^ (2 * m) / (2 ^ m * (m ! : ℝ))) := by
            rw [h2m]
            have h2p : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
            field_simp
            nlinarith [one_le_pow₀ (le_of_lt h) (n := m)]
        _ ≤ (m ! : ℝ) * 2 ^ m * Real.exp (x ^ 2 / 2) := by gcongr
    linarith

/-- A polynomial times the Gaussian, times any power of `|x|`, is bounded. -/
