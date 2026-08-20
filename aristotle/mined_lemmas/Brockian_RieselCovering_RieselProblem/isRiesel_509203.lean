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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is
composite for every `n ≥ 1`. -/

theorem isRiesel_509203 : IsRiesel 509203 := by
  refine ⟨⟨254601, by norm_num⟩, ?_⟩
  intro n hn hprime
  have hr : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hdvd := coverPrime_dvd n
  have hple : coverPrime (n % 24) ≤ 241 := coverPrime_le _ hr
  have hpp : Nat.Prime (coverPrime (n % 24)) := coverPrime_prime _ hr
  have hbig : 1018405 ≤ 509203 * 2 ^ n - 1 := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 509203 * 2 ≤ 509203 * 2 ^ n := Nat.mul_le_mul_left _ (by simpa using h2)
    omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ hdvd) with h | h
  · exact hpp.one_lt.ne' h
  · omega

/-- **The Riesel problem.**  The least Riesel number is at most `509203`, witnessed by the
covering set `{3, 5, 7, 13, 17, 241}` of the residues modulo `24`:  `509203` itself is a
Riesel number, i.e. `509203 * 2 ^ n - 1` is composite for every `n ≥ 1`.
(That `509203` is exactly the least such number is an open problem.) -/
