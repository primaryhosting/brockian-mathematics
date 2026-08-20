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

theorem coverPrime_dvd (n : ℕ) : coverPrime (n % 24) ∣ 509203 * 2 ^ n - 1 := by
  have hr : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  set r := n % 24
  set p := coverPrime r
  have h24 : (2 : ℕ) ^ 24 ≡ 1 [MOD p] := coverPrime_pow24 r hr
  have hq : ((2 : ℕ) ^ 24) ^ (n / 24) ≡ 1 [MOD p] := by
    simpa using h24.pow (n / 24)
  have hn : 24 * (n / 24) + r = n := Nat.div_add_mod n 24
  have hsplit : (2 : ℕ) ^ n = ((2 : ℕ) ^ 24) ^ (n / 24) * 2 ^ r := by
    rw [← pow_mul, ← pow_add, hn]
  have hbase : 509203 * 2 ^ r ≡ 1 [MOD p] := coverPrime_dvd_base r hr
  have hmain : 509203 * 2 ^ n ≡ 1 [MOD p] := by
    calc 509203 * 2 ^ n = ((2 : ℕ) ^ 24) ^ (n / 24) * (509203 * 2 ^ r) := by
          rw [hsplit]; ring
      _ ≡ 1 * 1 [MOD p] := hq.mul hbase
      _ = 1 := by ring
  have h1 : 1 ≤ 509203 * 2 ^ n := Nat.one_le_iff_ne_zero.2 (by positivity)
  exact (Nat.modEq_iff_dvd' h1).1 hmain.symm

