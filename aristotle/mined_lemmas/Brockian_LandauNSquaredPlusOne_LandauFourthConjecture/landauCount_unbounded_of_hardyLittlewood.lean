import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Filter Asymptotics

namespace Brockian
namespace LandauNSquaredPlusOne

/-! ## The statement

Landau's fourth problem asks whether there are infinitely many primes of the form `n ^ 2 + 1`.
This is an open problem, so the main theorem below is a *conditional reduction*: it derives the
conjecture from a Hardy–Littlewood style lower bound for the associated counting function.

Alongside it we prove a number of unconditional results:

* several reformulations of the conjecture (unboundedness of witnesses, unboundedness of the
  counting function, infinitude of the set of primes of the shape `n ^ 2 + 1`);
* the classical congruence restriction on the prime divisors of `n ^ 2 + 1`;
* the unconditional partial result that infinitely many primes divide *some* value `n ^ 2 + 1`.
-/

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime. -/

theorem landauCount_unbounded_of_hardyLittlewood (H : HardyLittlewoodLowerBound) :
    ∀ M : ℕ, ∃ N : ℕ, M < landauCount N := by
  obtain ⟨c, hc, hH⟩ := H
  intro M
  have hgrow : Tendsto (fun N : ℕ => c * (N : ℝ) / Real.log N) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => c * (x / Real.log x)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_div_log_atTop
    have h2 := h1.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h2.congr fun N => ?_
    simp [Function.comp, mul_div_assoc]
  obtain ⟨N, hN1, hN2⟩ := ((hgrow.eventually_ge_atTop ((M : ℝ) + 1)).and hH).exists
  refine ⟨N, ?_⟩
  have hle : (M : ℝ) + 1 ≤ (landauCount N : ℝ) := le_trans hN1 hN2
  have : (M : ℕ) + 1 ≤ landauCount N := by exact_mod_cast hle
  omega

/-- **Landau's fourth conjecture, conditionally.**  Assuming the Hardy–Littlewood style lower
bound `HardyLittlewoodLowerBound` for the counting function of primes of the form `n ^ 2 + 1`,
there are infinitely many natural numbers `n` such that `n ^ 2 + 1` is prime.

Landau's fourth problem is open, so the result is stated as a conditional reduction; the
hypothesis is a quantitative lower bound of the shape predicted by the Hardy–Littlewood
conjecture. -/
