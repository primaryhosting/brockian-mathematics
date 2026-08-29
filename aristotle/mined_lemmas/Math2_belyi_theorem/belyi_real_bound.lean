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

lemma belyi_real_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((m + n : ℝ)) ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) * x ^ m * (1 - x) ^ n ≤ 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1' : (0 : ℝ) ≤ 1 - x := by linarith
  set N : ℝ := (m : ℝ) + n with hN
  have hNpos : 0 < N := by positivity
  have key := amgm_two_weights m n (x * N / m) ((1 - x) * N / n) (by positivity) (by positivity)
    (by field_simp; ring)
  have hx : (x * N / m) ^ m * ((1 - x) * N / n) ^ n
      = N ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) * x ^ m * (1 - x) ^ n := by
    rw [div_pow, div_pow, mul_pow, mul_pow, pow_add]
    field_simp
  rw [hx] at key
  exact key

/-- `B_{m,n}` maps the rational points of the unit interval into the unit interval. -/
