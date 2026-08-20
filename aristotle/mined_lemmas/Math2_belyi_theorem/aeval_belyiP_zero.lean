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
Target: `Math2.belyi_theorem`
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file formalizes Belyi's theorem for the projective line with marked points, i.e. for the
curves `ℙ¹ \ S` where `S` is a finite set of points: such a marked curve is defined over `ℚ̄`
(all points of `S` are algebraic numbers) if and only if there is a Belyi map, i.e. a nonconstant
map `ℙ¹ → ℙ¹` defined over `ℚ` which is ramified only above `{0, 1, ∞}` and which sends `S`
into `{0, 1, ∞}`.

Belyi maps are realized here by polynomials `f ∈ ℚ[X]`; such an `f`, viewed as a self-map of
`ℙ¹`, sends `∞` to `∞`, so ramification above `∞` is automatic and the condition on the
ramification is that all *finite* critical values lie in `{0, 1}`.  This is `Math2.IsBelyi`.

The main result is `Math2.belyi_theorem`.  The non-trivial direction is Belyi's construction,
which is carried out in two steps:

* `Math2.rationalize`: composing with a suitable polynomial over `ℚ` one can force all critical
  values to be rational.  This is the induction on the degrees over `ℚ` of the critical values,
  using that composing with the minimal polynomial of a critical value of maximal degree `D`
  strictly decreases the number of critical values of degree `D`.
* `Math2.rat_reduction`: any finite set of *rational* points can be pushed into `{0, 1}` by a
  Belyi polynomial.  This is Belyi's classical argument with the polynomials
  `x ↦ c · x ^ a (1 - x) ^ n` (`Math2.belyiP`), which have all their critical values in `{0, 1}`
  and collapse `{0, 1, a / (a + n)}` into `{0, 1}`, combined with affine normalizations.
-/

open Polynomial

set_option maxHeartbeats 1000000

namespace Math2

noncomputable section

/-- The degree over `ℚ` of a complex number (`0` if transcendental). -/

lemma aeval_belyiP_zero (a n : ℕ) (ha : 0 < a) :
    aeval (0 : A) (belyiP a n) = 0 := by
  rw [aeval_belyiP]
  simp [zero_pow ha.ne']

omit [CharZero A] in
