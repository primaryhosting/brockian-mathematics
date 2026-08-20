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

lemma belyiP_crit (a n : ℕ) (ha : 0 < a) (hn : 0 < n) (z : A)
    (hz : aeval z (derivative (belyiP a n)) = 0) :
    aeval z (belyiP a n) = 0 ∨ aeval z (belyiP a n) = 1 := by
  have ha' : (a : A) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hn' : (n : A) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hs : (a : A) + (n : A) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := A) (n := a + n) |>.2 (by omega : a + n ≠ 0)
    simpa using h
  by_cases hz0 : z = 0
  · left; rw [hz0]; exact aeval_belyiP_zero a n ha
  by_cases hz1 : z = 1
  · left; rw [hz1]; exact aeval_belyiP_one a n hn
  right
  rw [aeval_derivative_belyiP] at hz
  have hbr : (a : A) * z ^ (a - 1) * (1 - z) ^ n - (n : A) * z ^ a * (1 - z) ^ (n - 1) = 0 := by
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (algebraMap_belyiC_ne_zero a n ha hn)
    · exact h
  have hza : z ^ a = z ^ (a - 1) * z := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ]
  have hzn : (1 - z) ^ n = (1 - z) ^ (n - 1) * (1 - z) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hza, hzn] at hbr
  have hfac : z ^ (a - 1) * (1 - z) ^ (n - 1) * ((a : A) * (1 - z) - (n : A) * z) = 0 := by
    linear_combination hbr
  have h1 : z ^ (a - 1) ≠ 0 := pow_ne_zero _ hz0
  have h2 : (1 - z) ^ (n - 1) ≠ 0 :=
    pow_ne_zero _ (fun h => hz1 (by linear_combination -h))
  have h3 : (a : A) * (1 - z) - (n : A) * z = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' h1
      · exact absurd h' h2
    · exact h
  have hzval : z = (a : A) / ((a : A) + (n : A)) := by
    rw [eq_div_iff hs]; linear_combination -h3
  rw [hzval]
  exact aeval_belyiP_lambda a n ha hn

