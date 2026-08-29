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

-- # Sophie Germain Infinitude
-- Category: Brockian Conjecture
-- Target: Brockian.SophieGermain.SophieGermainInfinitude
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem dvd_mersenne_of_isSophieGermain {p : ℕ} (hp : IsSophieGermain p) (h4 : p % 4 = 3)
    (hp3 : 3 < p) : (2 * p + 1) ∣ 2 ^ p - 1 := by
  set q := 2 * p + 1 with hqdef
  haveI : Fact (Nat.Prime q) := ⟨hp.2⟩
  have hq8 : q % 8 = 7 := by omega
  have hsq : IsSquare (2 : ZMod q) :=
    (ZMod.exists_sq_eq_two_iff (by omega)).mpr (Or.inr hq8)
  have h2ne : (2 : ZMod q) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    simpa using h
  have hcrit := (ZMod.euler_criterion q h2ne).mp hsq
  have hqhalf : q / 2 = p := by omega
  rw [hqhalf] at hcrit
  have hcast : ((2 ^ p : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; simpa using hcrit
  have hmod : 2 ^ p ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm

/-- For a Sophie Germain prime `p > 3` with `p ≡ 3 (mod 4)`, the Mersenne number `2 ^ p - 1`
is composite. -/
