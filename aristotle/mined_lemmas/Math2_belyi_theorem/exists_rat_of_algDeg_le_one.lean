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

lemma exists_rat_of_algDeg_le_one {s : ℂ} (hs : IsIntegral ℚ s) (h : algDeg s ≤ 1) :
    ∃ q : ℚ, s = (q : ℂ) := by
  have h1 : algDeg s = 1 := le_antisymm h (algDeg_pos hs)
  rw [algDeg, minpoly.natDegree_eq_one_iff] at h1
  obtain ⟨q, hq⟩ := h1
  exact ⟨q, by simp [← hq]⟩

open Classical in
/-- A choice of rational number representing a complex number, when possible. -/
