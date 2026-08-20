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

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- The Riesel number under consideration. -/

theorem covPrime_dvd (n : ℕ) : covPrime (n % 24) ∣ k * 2 ^ n - 1 := by
  have hd : covPrime (n % 24) ∣ M := covPrime_dvd_M _
  have h1 : k * 2 ^ n ≡ k * 2 ^ (n % 24) [MOD covPrime (n % 24)] :=
    Nat.ModEq.of_dvd hd ((two_pow_modEq n).mul_left k)
  have h2 : k * 2 ^ (n % 24) ≡ 1 [MOD covPrime (n % 24)] :=
    key_modEq _ (Nat.mod_lt _ (by norm_num))
  have h3 : (1 : ℕ) ≡ k * 2 ^ n [MOD covPrime (n % 24)] := (h1.trans h2).symm
  have hle : (1 : ℕ) ≤ k * 2 ^ n := Nat.mul_pos (by norm_num [k]) (Nat.two_pow_pos n)
  exact (Nat.modEq_iff_dvd' hle).mp h3

/-- **The Riesel problem**: `509203` is a Riesel number, i.e. `509203 * 2 ^ n - 1` is
composite (never prime) for every `n ≥ 1`. -/
