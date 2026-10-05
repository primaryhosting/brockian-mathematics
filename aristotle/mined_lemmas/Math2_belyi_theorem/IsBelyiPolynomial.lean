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

lemma IsBelyiPolynomial.comp {f g : ℚ[X]} (hf : 0 < f.natDegree) (hg : IsBelyiPolynomial g)
    (hcrit : ∀ z : ℂ, aeval z (derivative f) = 0 →
      aeval (aeval z f) g = 0 ∨ aeval (aeval z f) g = 1) :
    IsBelyiPolynomial (g.comp f) := by
  refine ⟨?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hg.1 hf
  · intro z hz
    rw [derivative_comp] at hz
    simp only [map_mul, aeval_comp] at hz
    rw [aeval_comp]
    rcases mul_eq_zero.1 hz with h | h
    · exact hcrit z h
    · exact hg.2 _ h

