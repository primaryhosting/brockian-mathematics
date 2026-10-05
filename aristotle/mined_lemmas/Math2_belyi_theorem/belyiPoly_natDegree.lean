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

lemma belyiPoly_natDegree {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (belyiPoly m n).natDegree = m + n := by
  have hc : bcoef m n ≠ 0 := (bcoef_pos hm hn).ne'
  have h1 : ((1 : ℚ[X]) - X).natDegree = 1 := by
    have h : ((1 : ℚ[X]) - X) = -(X - C 1) := by simp only [C_1]; ring
    rw [h, natDegree_neg, natDegree_X_sub_C]
  unfold belyiPoly
  rw [natDegree_mul, natDegree_mul, natDegree_C, natDegree_pow, natDegree_pow, natDegree_X, h1]
  · ring
  · exact (C_ne_zero.mpr hc)
  · exact pow_ne_zero _ X_ne_zero
  · exact mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero _ X_ne_zero)
  · refine pow_ne_zero _ ?_
    intro h
    have := congrArg (fun p => Polynomial.eval (0 : ℚ) p) h
    simp at this

/-- The derivative of `B_{m,n}` factors as `c · X^(m-1) (1-X)^(n-1) (m - (m+n) X)`. -/
