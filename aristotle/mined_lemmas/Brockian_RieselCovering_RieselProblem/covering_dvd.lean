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

namespace Brockian.RieselCovering

/-- A *Riesel number* is a positive odd natural number `k` such that `k * 2 ^ n - 1`
is composite (never prime) for every `n ≥ 1`. -/

theorem covering_dvd {p r n : ℕ} (hp : p ∣ 16777215) (hr : n % 24 = r)
    (hdvd : p ∣ 509203 * 2 ^ r - 1) : p ∣ 509203 * 2 ^ n - 1 := by
  have h1 : (1 : ℕ) ≤ 509203 * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : (1 : ℕ) ≤ 509203 * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmod : (509203 : ℕ) * 2 ^ n ≡ 509203 * 2 ^ r [MOD p] := by
    have := (two_pow_modEq n).of_dvd hp
    rw [hr] at this
    exact this.mul_left _
  have hr1 : (1 : ℕ) ≡ 509203 * 2 ^ r [MOD p] := (Nat.modEq_iff_dvd' h1).mpr hdvd
  exact (Nat.modEq_iff_dvd' h2).mp (hr1.trans hmod.symm)

/-- `509203` is a Riesel number: `509203 * 2 ^ n - 1` is never prime for `n ≥ 1`.
The proof uses the covering set `{3, 5, 7, 13, 17, 241}` of period `24`. -/
