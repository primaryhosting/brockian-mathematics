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

lemma exists_ratBelyi (S : Finset ℚ) (hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1) :
    ∃ f : ℚ[X], RatBelyi S f :=
  exists_ratBelyi_aux _ S hS le_rfl

/-- Belyi's construction for an arbitrary finite set of rational numbers: there is a
non-constant `f ∈ ℚ[X]`, all of whose finite critical values lie in `{0,1}`, taking every
element of `S` to `0` or `1`. -/
