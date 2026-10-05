import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

lemma amgm_two_weights (m n : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : (m : ℝ) * u + (n : ℝ) * v = (m : ℝ) + (n : ℝ)) : u ^ m * v ^ n ≤ 1 := by
  have h1 : u ≤ Real.exp (u - 1) := by have := Real.add_one_le_exp (u - 1); linarith
  have h2 : v ≤ Real.exp (v - 1) := by have := Real.add_one_le_exp (v - 1); linarith
  have h3 : u ^ m ≤ Real.exp ((m : ℝ) * (u - 1)) := by
    calc u ^ m ≤ (Real.exp (u - 1)) ^ m := pow_le_pow_left₀ hu h1 m
    _ = Real.exp ((m : ℝ) * (u - 1)) := by rw [← Real.exp_nat_mul]
  have h4 : v ^ n ≤ Real.exp ((n : ℝ) * (v - 1)) := by
    calc v ^ n ≤ (Real.exp (v - 1)) ^ n := pow_le_pow_left₀ hv h2 n
    _ = Real.exp ((n : ℝ) * (v - 1)) := by rw [← Real.exp_nat_mul]
  calc u ^ m * v ^ n ≤ Real.exp ((m : ℝ) * (u - 1)) * Real.exp ((n : ℝ) * (v - 1)) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = Real.exp ((m : ℝ) * u + (n : ℝ) * v - ((m : ℝ) + (n : ℝ))) := by
        rw [← Real.exp_add]; ring_nf
    _ = 1 := by rw [h]; simp

