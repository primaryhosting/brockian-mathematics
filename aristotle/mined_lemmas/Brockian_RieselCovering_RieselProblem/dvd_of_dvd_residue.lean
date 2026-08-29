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

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is never prime
for `n ≥ 1`. -/

lemma dvd_of_dvd_residue (p r n : ℕ) (h24 : 2 ^ 24 ≡ 1 [MOD p]) (hr : n % 24 = r)
    (hd : p ∣ 509203 * 2 ^ r - 1) : p ∣ 509203 * 2 ^ n - 1 := by
  have h1 : ∀ m : ℕ, 1 ≤ 509203 * 2 ^ m := by
    intro m
    have : 0 < 2 ^ m := pow_pos (by norm_num) m
    nlinarith
  have hone : 1 ≡ 509203 * 2 ^ r [MOD p] := (Nat.modEq_iff_dvd' (h1 r)).mpr hd
  have hstep : 509203 * 2 ^ r ≡ 509203 * 2 ^ n [MOD p] := by
    have := (two_pow_modEq_two_pow_mod p n h24).symm
    rw [hr] at this
    exact Nat.ModEq.mul_left _ this
  exact (Nat.modEq_iff_dvd' (h1 n)).mp (hone.trans hstep)

/-- The covering set `{3, 5, 7, 13, 17, 241}` for `k = 509203`: for every exponent `n`
one of these primes divides `509203 * 2 ^ n - 1`. -/
