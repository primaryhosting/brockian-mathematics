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

def RatBelyi (S : Finset ℚ) (f : ℚ[X]) : Prop :=
  IsBelyiPolynomial f ∧ (∀ x ∈ S, f.eval x = 0 ∨ f.eval x = 1) ∧
    (f.eval 0 = 0 ∨ f.eval 0 = 1) ∧ (f.eval 1 = 0 ∨ f.eval 1 = 1) ∧
    (∀ x : ℚ, 0 ≤ x → x ≤ 1 → 0 ≤ f.eval x ∧ f.eval x ≤ 1)

/-- Writing a rational number in `(0,1)` as `m/(m+n)` with `m, n` positive naturals. -/
