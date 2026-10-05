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

lemma belyiPoly_eval_lambda {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (belyiPoly m n).eval ((m : ℚ) / ((m : ℚ) + n)) = 1 := by
  have hm' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hN : (0 : ℚ) < (m : ℚ) + n := by linarith
  have h1 : (1 : ℚ) - (m : ℚ) / ((m : ℚ) + n) = (n : ℚ) / ((m : ℚ) + n) := by
    field_simp; ring
  rw [belyiPoly_eval, h1]
  unfold bcoef
  rw [div_pow, div_pow, pow_add]
  field_simp

