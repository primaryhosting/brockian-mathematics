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

lemma belyiPoly_eval_mem_Icc {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℚ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (belyiPoly m n).eval x ∧ (belyiPoly m n).eval x ≤ 1 := by
  have hc := bcoef_pos hm hn
  have hx1' : (0 : ℚ) ≤ 1 - x := by linarith
  refine ⟨?_, ?_⟩
  · rw [belyiPoly_eval]
    positivity
  · rw [belyiPoly_eval]
    have hreal := belyi_real_bound m n hm hn (x : ℝ) (by exact_mod_cast hx0) (by exact_mod_cast hx1)
    have hcast : ((bcoef m n * x ^ m * (1 - x) ^ n : ℚ) : ℝ)
        = ((m + n : ℝ)) ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) * (x : ℝ) ^ m * (1 - (x : ℝ)) ^ n := by
      unfold bcoef
      push_cast
      ring
    have : ((bcoef m n * x ^ m * (1 - x) ^ n : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
      rw [hcast]; simpa using hreal
    exact_mod_cast this

end UnitInterval

end Math2

/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any command, so the header above is a plain
-- block comment rather than a module docstring.)

import RequestProject.BelyiRat

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Belyi's theorem for the projective line with marked points

We work with the following concrete incarnation of the theorem.  A *Belyi map* here is a
non-constant polynomial `f ∈ ℚ[X]`, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`; equivalently, `f` is unramified outside the fibre over
`{0, 1, ∞}` (the point `∞` is totally ramified for a polynomial).  This is `IsBelyiPolynomial`.

The curve under consideration is the projective line together with a finite set `S ⊆ ℂ` of marked
points, and "defined over `ℚ̄`" means that every marked point is algebraic over `ℚ`.

`Math2.belyi_theorem` states that the marked points are defined over `ℚ̄` if and only if there is a
Belyi map taking every marked point into `{0, 1} ⊆ f⁻¹({0,1,∞})`.

The easy direction is that a point sent to `0` or `1` by a nonzero rational polynomial is
algebraic.  The substantive direction is Belyi's construction: first the degrees of the marked
points are reduced by repeatedly applying minimal polynomials (each such step adds the critical
values of the minimal polynomial to the set of marked points, but these have strictly smaller
degree), and then the resulting rational marked points are pushed into `{0, 1}` by the
polynomials `x ↦ c · x^m (1-x)^n` of `RequestProject.BelyiPoly`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial IntermediateField

/-- The degree over `ℚ` of a complex number. -/
