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

import Mathlib

/-!
## Overview

The Fermat numbers are `Fₙ = 2 ^ (2 ^ n) + 1` (`Nat.fermatNumber` in Mathlib).  The
five numbers `F₀ = 3`, `F₁ = 5`, `F₂ = 17`, `F₃ = 257`, `F₄ = 65537` are prime, and no other
Fermat prime is known; whether some `Fₙ` with `n > 4` is prime is a famous open question.

This file does not settle that question.  Instead it gives a *Lean-checked conditional
reduction*: the main theorem `Brockian.FermatNumbers.FermatPrimeBeyondFour` shows that for
every `n > 4`,

  `Fₙ` is prime  ↔  `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`,

i.e. **Pépin's test** is not only sufficient but also necessary.  The sufficiency direction is
Mathlib's `Nat.pepin_primality'`; the necessity direction (`pepin_necessity` below) is proved
here from quadratic reciprocity: `Fₙ ≡ 1 [MOD 4]` and `Fₙ ≡ 2 [MOD 3]` for `n ≥ 1`, so `3` is a
quadratic non-residue modulo a prime `Fₙ`, and Euler's criterion gives the claim.

Consequently the existence of a Fermat prime beyond `F₄` is equivalent to a purely
computational statement (`exists_fermatPrime_beyond_four_iff_pepin`).

We also record the classical numerical facts framing the problem: `F₀, …, F₄` are prime while
`F₅, F₆, F₇` are composite.
-/

namespace Brockian.FermatNumbers

open Nat ZMod

/-! ### The known Fermat primes and the first composite Fermat numbers -/

theorem fermatNumber_zero_prime : (Nat.fermatNumber 0).Prime := by
  rw [show Nat.fermatNumber 0 = 3 from rfl]; norm_num

theorem fermatNumber_one_prime : (Nat.fermatNumber 1).Prime := by
  rw [show Nat.fermatNumber 1 = 5 from rfl]; norm_num

theorem fermatNumber_two_prime : (Nat.fermatNumber 2).Prime := by
  rw [show Nat.fermatNumber 2 = 17 from rfl]; norm_num

theorem fermatNumber_three_prime : (Nat.fermatNumber 3).Prime := by
  rw [show Nat.fermatNumber 3 = 257 from rfl]; norm_num

theorem fermatNumber_four_prime : (Nat.fermatNumber 4).Prime := by
  rw [show Nat.fermatNumber 4 = 65537 from rfl]; norm_num

/-- `F₅ = 4294967297 = 641 * 6700417` is not prime (Euler). -/
theorem fermatNumber_five_not_prime : ¬ (Nat.fermatNumber 5).Prime := by
  rw [show Nat.fermatNumber 5 = 641 * 6700417 from rfl]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- `F₆ = 274177 * 67280421310721` is not prime. -/
theorem fermatNumber_six_not_prime : ¬ (Nat.fermatNumber 6).Prime := by
  rw [show Nat.fermatNumber 6 = 274177 * 67280421310721 from rfl]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- `F₇ = 59649589127497217 * 5704689200685129054721` is not prime. -/
theorem fermatNumber_seven_not_prime : ¬ (Nat.fermatNumber 7).Prime := by
  rw [show Nat.fermatNumber 7 = 59649589127497217 * 5704689200685129054721 from rfl]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-! ### Arithmetic of Fermat numbers modulo `3` and `4` -/

theorem fermatNumber_mod_four (n : ℕ) (hn : 0 < n) : Nat.fermatNumber n % 4 = 1 := by
  have h2n : 2 ≤ 2 ^ n := by
    calc (2:ℕ) = 2 ^ 1 := rfl
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 2 := ⟨2 ^ n - 2, by omega⟩
  rw [Nat.fermatNumber, hk, pow_add]
  omega

theorem fermatNumber_mod_three (n : ℕ) (hn : 0 < n) : Nat.fermatNumber n % 3 = 2 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 2 * m := ⟨2 ^ (n - 1), by
    conv_lhs => rw [show n = 1 + (n - 1) by omega]
    rw [pow_add]; ring⟩
  have h : (2 : ℕ) ^ (2 ^ n) % 3 = 1 := by
    rw [hm, pow_mul, Nat.pow_mod]
    norm_num
  rw [Nat.fermatNumber]
  omega

/-- Halving `Fₙ - 1` is the same as halving `Fₙ` in `ℕ`, since `Fₙ` is odd. -/
theorem fermatNumber_sub_one_div_two (n : ℕ) :
    (Nat.fermatNumber n - 1) / 2 = Nat.fermatNumber n / 2 := by
  have h : (2 : ℕ) ^ (2 ^ n) = 2 * 2 ^ (2 ^ n - 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    conv_lhs => rw [show 2 ^ n = 1 + (2 ^ n - 1) by omega]
    rw [pow_add]; ring
  rw [Nat.fermatNumber]
  omega

/-! ### Necessity of Pépin's criterion -/

/-- `2` is not a square modulo `3`. -/
theorem not_isSquare_two_zmod_three : ¬ IsSquare (2 : ZMod 3) := by decide

/-- If `Fₙ` (`n ≥ 1`) is prime, then `3` is a quadratic non-residue modulo `Fₙ`. -/
theorem not_isSquare_three_of_prime (n : ℕ) (hn : 0 < n) (hp : (Nat.fermatNumber n).Prime) :
    ¬ IsSquare ((3 : ℕ) : ZMod (Nat.fermatNumber n)) := by
  haveI : Fact (Nat.fermatNumber n).Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcast : ((Nat.fermatNumber n : ℕ) : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, fermatNumber_mod_three n hn]
    norm_num
  rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (fermatNumber_mod_four n hn) (by norm_num),
    hcast]
  exact not_isSquare_two_zmod_three

/-- **Necessity of Pépin's test.** If `Fₙ` is prime for some `n ≥ 1`, then
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`.  (This is the converse of Mathlib's
`Nat.pepin_primality'`.) -/
theorem pepin_necessity (n : ℕ) (hn : 0 < n) (hp : (Nat.fermatNumber n).Prime) :
    (3 : ZMod (Nat.fermatNumber n)) ^ ((Nat.fermatNumber n - 1) / 2) = -1 := by
  haveI : Fact (Nat.fermatNumber n).Prime := ⟨hp⟩
  have hleg : legendreSym (Nat.fermatNumber n) 3 = -1 :=
    (legendreSym.eq_neg_one_iff' _).mpr (not_isSquare_three_of_prime n hn hp)
  have h := legendreSym.eq_pow (Nat.fermatNumber n) 3
  rw [hleg] at h
  push_cast at h
  rw [fermatNumber_sub_one_div_two, h]

/-- **Pépin's test**, as an equivalence, for every `n ≥ 1`. -/
theorem pepin_test (n : ℕ) (hn : 0 < n) :
    (Nat.fermatNumber n).Prime ↔
      (3 : ZMod (Nat.fermatNumber n)) ^ ((Nat.fermatNumber n - 1) / 2) = -1 :=
  ⟨pepin_necessity n hn, Nat.pepin_primality' n⟩

/-! ### Main statement -/

/-- **Fermat prime beyond four (conditional reduction).**

Whether there is a Fermat prime `Fₙ = 2 ^ (2 ^ n) + 1` with `n > 4` is an open problem; this
theorem reduces it, for each individual `n > 4`, to the modular criterion of Pépin:
`Fₙ` is prime if and only if `3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`.

The hypothesis `4 < n` is what the statement of the problem asks for; the proof in fact only
uses `0 < n` (see `pepin_test`). -/
theorem FermatPrimeBeyondFour (n : ℕ) (hn : 4 < n) :
    (Nat.fermatNumber n).Prime ↔
      (3 : ZMod (Nat.fermatNumber n)) ^ ((Nat.fermatNumber n - 1) / 2) = -1 :=
  pepin_test n (by omega)

/-- The existence of a Fermat prime beyond `F₄` is equivalent to the existence of some `n > 4`
passing Pépin's congruence. -/
theorem exists_fermatPrime_beyond_four_iff_pepin :
    (∃ n, 4 < n ∧ (Nat.fermatNumber n).Prime) ↔
      (∃ n, 4 < n ∧ (3 : ZMod (Nat.fermatNumber n)) ^ ((Nat.fermatNumber n - 1) / 2) = -1) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, (FermatPrimeBeyondFour n hn).1 hp⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (FermatPrimeBeyondFour n hn).2 h⟩

end Brockian.FermatNumbers

