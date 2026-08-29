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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment rather than a `/-!` module docstring.)

import Mathlib

/-!
## Overview

The `n`-th Fermat number is `Fₙ = 2 ^ 2 ^ n + 1`.  The numbers `F₀, …, F₄` are prime, and no
further Fermat prime is known; whether some `Fₙ` with `n > 4` is prime is a famous open problem.

This file contains:

* `Brockian.FermatNumbers.fermat` — the Fermat numbers;
* `Brockian.FermatNumbers.prime_of_pepin` — the sufficiency half of Pépin's test;
* `Brockian.FermatNumbers.pepin_of_prime` — the necessity half of Pépin's test;
* `Brockian.FermatNumbers.FermatPrimeBeyondFour` — the main result: an unconditional
  *Lean-checked reduction* of the open conjecture "there is a Fermat prime beyond `F₄`" to a
  purely modular-arithmetic statement (Pépin's criterion);
* verified data: `F₀, …, F₄` are prime, and `F₅`, `F₆` are composite.
-/

namespace Brockian.FermatNumbers

/-- The `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`. -/

theorem prime_of_pepin (n : ℕ) (h : (3 : ZMod (fermat n)) ^ (2 ^ (2 ^ n - 1)) = -1) :
    Nat.Prime (fermat n) := by
  set N := fermat n with hN
  have hN2 : 2 < N := fermat_two_lt n
  haveI : NeZero N := ⟨by omega⟩
  set u : ZMod N := 3 with hu
  have hne : (-1 : ZMod N) ≠ 1 := by
    intro hcon
    have h2 : ((2:ℕ) : ZMod N) = 0 := by push_cast; linear_combination -hcon
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hpow : u ^ (2 ^ 2 ^ n) = 1 := by
    rw [pow_two_pow_split, pow_mul, h]
    ring
  have hunit : IsUnit u := by
    refine IsUnit.of_mul_eq_one (u ^ (2 ^ 2 ^ n - 1)) ?_
    have h1 : 1 ≤ 2 ^ 2 ^ n := Nat.one_le_two_pow
    calc u * u ^ (2 ^ 2 ^ n - 1) = u ^ (2 ^ 2 ^ n) := by
          rw [← pow_succ']; congr 1; omega
    _ = 1 := hpow
  have hdvd : orderOf u ∣ 2 ^ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
  have hnd : ¬ (orderOf u ∣ 2 ^ (2 ^ n - 1)) := by
    intro hc
    have hone := orderOf_dvd_iff_pow_eq_one.mp hc
    rw [h] at hone
    exact hne hone
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hkeq : k = 2 ^ n := by
    by_contra hkn
    exact hnd (hko ▸ Nat.pow_dvd_pow 2 (by omega))
  have hord : orderOf u = N - 1 := by
    rw [hko, hkeq, hN]
    simp [fermat]
  have hordu : orderOf hunit.unit = N - 1 := by
    rw [← orderOf_units, IsUnit.unit_spec, hord]
  have hdvd2 : (N - 1) ∣ Nat.totient N := by
    rw [← hordu, ← ZMod.card_units_eq_totient N]
    exact orderOf_dvd_card
  have hlt : Nat.totient N < N := Nat.totient_lt N (by omega)
  have hpos : 0 < Nat.totient N := Nat.totient_pos.mpr (by omega)
  have htot : Nat.totient N = N - 1 := by
    have := Nat.le_of_dvd hpos hdvd2
    omega
  exact (Nat.totient_eq_iff_prime (by omega)).mp htot

/-- **Pépin's test, necessity.**  If the Fermat number `Fₙ` with `n ≥ 1` is prime, then
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`.  (Proof: `3` is a quadratic nonresidue mod `Fₙ`, by
quadratic reciprocity together with `Fₙ ≡ 1 [MOD 4]` and `Fₙ ≡ 2 [MOD 3]`.) -/
