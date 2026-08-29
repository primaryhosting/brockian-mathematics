/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalised here

Belyi's theorem says that a smooth projective curve is defined over `ℚ̄` if and only if it admits
a map to `ℙ¹` ramified only over `{0, 1, ∞}`.  The substantial half of Belyi's proof is the
*Belyi reduction*: an explicit algorithm which, starting from a map whose branch locus is a finite
set of algebraic points, composes it with suitable polynomials until the branch locus is contained
in `{0, 1, ∞}`.

This file formalises that algorithm over `ℚ`, in the self-contained form of an equivalence
(the statement `Math2.belyi_theorem`):

> a set `S ⊆ ℚ` is finite **iff** there is a non-constant `P ∈ ℚ[X]` which maps `S` into `{0,1}`
> and all of whose finite critical values lie in `{0,1}`.

Viewed as a self-map of `ℙ¹`, such a `P` is unramified outside `{0, 1, ∞}` (a polynomial is
totally ramified over `∞`), i.e. it *is* a Belyi map for `ℙ¹` which moreover kills the prescribed
set `S` of marked points.  The forward direction is the Belyi reduction algorithm (normalise `S`
by an affine map, then repeatedly compose with the Belyi polynomials
`c · x^m (1-x)^n`, each step lowering the number of bad values); the backward direction says that
only finitely many points can be marked this way, since `P⁻¹{0,1}` is finite.
-/

open Polynomial

namespace Math2

/-- A polynomial `P ∈ ℚ[X]` is a *Belyi polynomial* if it is non-constant and all of its finite
critical values lie in `{0, 1}`.  Viewed as a map `ℙ¹ → ℙ¹`, such a `P` is unramified outside
`{0, 1, ∞}`, the point `∞` being totally ramified for every polynomial. -/

lemma isBelyiPoly_belyiPoly (m n : ℕ) : IsBelyiPoly (belyiPoly m n) := by
  have hc := belyiPoly_const_ne_zero m n
  refine ⟨natDegree_pos_of_eval_ne (x := 0) (y := (m + 1 : ℚ) / (m + n + 2)) ?_, ?_⟩
  · rw [eval_belyiPoly_zero, eval_belyiPoly_crit]
    exact zero_ne_one
  · intro x hx
    rw [eval_derivative_belyiPoly] at hx
    have hM : (m + n + 2 : ℚ) ≠ 0 := by positivity
    rcases mul_eq_zero.mp hx with hx' | hx'
    · rcases mul_eq_zero.mp hx' with hx'' | hx''
      · rcases mul_eq_zero.mp hx'' with h | h
        · exact absurd h hc
        · -- `x ^ m = 0` forces `x = 0`
          have hx0 : x = 0 := pow_eq_zero_iff'.mp h |>.1
          subst hx0
          left; exact eval_belyiPoly_zero m n
      · have hx1 : (1 : ℚ) - x = 0 := pow_eq_zero_iff'.mp hx'' |>.1
        have : x = 1 := by linarith
        subst this
        left; exact eval_belyiPoly_one m n
    · have : x = (m + 1 : ℚ) / (m + n + 2) := by
        field_simp
        linarith
      subst this
      right; exact eval_belyiPoly_crit m n

/-! ### The Belyi reduction algorithm -/

/-- Every rational number strictly between `0` and `1` is of the form `(m+1)/(m+n+2)`. -/
