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

lemma aeval_rat_mem {f : ℚ[X]} {q : ℚ} (h : f.eval q = 0 ∨ f.eval q = 1) :
    aeval (q : ℂ) f = 0 ∨ aeval (q : ℂ) f = 1 := by
  rw [aeval_rat]
  rcases h with h | h <;> rw [h] <;> simp

/-- Main induction: a Belyi polynomial sending a finite set of rationals of `[0,1]` into `{0,1}`,
which moreover fixes the unit interval and sends `0, 1` into `{0,1}`. -/
