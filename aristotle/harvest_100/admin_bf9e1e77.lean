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
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`, so the
-- requested header is repeated verbatim as the module docstring just below the import.)

import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

`Nat.fermatNumber n = 2 ^ (2 ^ n) + 1` is Mathlib's definition of the `n`-th Fermat number.
The numbers `F₀, …, F₄` are prime and no further Fermat prime is known; whether some `Fₙ` with
`n > 4` is prime is a well-known open problem.

Accordingly, the target theorem `FermatPrimeBeyondFour` is stated and proved here as an
unconditional *reduction*: a Fermat prime with index `n > 4` exists if and only if some `Fₙ`
with `n > 4` passes **Pépin's test** `3 ^ ((Fₙ - 1) / 2) ≡ -1 (mod Fₙ)`.

The `←` direction is Mathlib's `Nat.pepin_primality`
(`Mathlib/NumberTheory/Fermat.lean`), which is the "existing lemma that nearly closes this".
The `→` direction (`pepin_of_prime`) is proved here from quadratic reciprocity, in the form of
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, together with Euler's criterion in the form
`legendreSym.eq_pow`.

Unconditional companion facts (`F₄ = 65537` is prime, `F₅` is composite) are proved at the end.
-/

namespace Brockian.FermatNumbers

open Nat

/-- For `n ≥ 1`, the Fermat number `Fₙ = 2 ^ (2 ^ n) + 1` is `1` modulo `4`. -/
lemma fermatNumber_mod_four (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 4 = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 2 + m :=
    ⟨2 ^ n - 2, by have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hn; simp at this; omega⟩
  rw [Nat.fermatNumber, hm, pow_add, add_comm]
  simp

/-- For `n ≥ 1`, the Fermat number `Fₙ = 2 ^ (2 ^ n) + 1` is `2` modulo `3`. -/
lemma fermatNumber_mod_three (n : ℕ) (hn : 1 ≤ n) : Nat.fermatNumber n % 3 = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 2 * k := ⟨2 ^ (n - 1), by rw [← pow_succ']; congr 1; omega⟩
  rw [Nat.fermatNumber, hk, pow_mul]
  have h : (2 ^ 2) ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  omega

/-- `(Fₙ - 1) / 2 = Fₙ / 2 = 2 ^ (2 ^ n - 1)`. -/
lemma fermatNumber_div_two (n : ℕ) : Nat.fermatNumber n / 2 = 2 ^ (2 ^ n - 1) := by
  have h : 2 ^ (2 ^ n) = 2 * 2 ^ (2 ^ n - 1) := by
    rw [← pow_succ']
    congr 1
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [Nat.fermatNumber, h]
  omega

/-- If `Fₙ` (`n ≥ 1`) is prime, then `3` is a quadratic nonresidue modulo `Fₙ`.
Indeed `Fₙ ≡ 1 [MOD 4]`, so by quadratic reciprocity `3` is a square mod `Fₙ` iff `Fₙ` is a
square mod `3`; but `Fₙ ≡ 2 [MOD 3]` and `2` is not a square mod `3`. -/
lemma not_isSquare_three (n : ℕ) (hn : 1 ≤ n) (hp : (Nat.fermatNumber n).Prime) :
    ¬ IsSquare (3 : ZMod (Nat.fermatNumber n)) := by
  haveI : Fact (Nat.fermatNumber n).Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have key := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := Nat.fermatNumber n) (q := 3)
    (fermatNumber_mod_four n hn) (by norm_num)
  intro hs
  have h2 : IsSquare ((Nat.fermatNumber n : ℕ) : ZMod 3) := key.mp (by push_cast; exact hs)
  rw [← ZMod.natCast_mod, fermatNumber_mod_three n hn] at h2
  revert h2
  decide

/-- The converse direction of **Pépin's test**: if `Fₙ` is prime (`n ≥ 1`) then
`3 ^ (2 ^ (2 ^ n - 1)) = -1` in `ZMod Fₙ`.  This is Euler's criterion applied to the
quadratic nonresidue `3`. -/
theorem pepin_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : (Nat.fermatNumber n).Prime) :
    (3 : ZMod (Nat.fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1 := by
  haveI : Fact (Nat.fermatNumber n).Prime := ⟨hp⟩
  have hl : legendreSym (Nat.fermatNumber n) 3 = -1 :=
    (legendreSym.eq_neg_one_iff _).mpr (by push_cast; exact not_isSquare_three n hn hp)
  have h := legendreSym.eq_pow (p := Nat.fermatNumber n) 3
  rw [hl, fermatNumber_div_two] at h
  push_cast at h
  exact h.symm

/-- **Pépin's test** (full equivalence), for `n ≥ 1`: the Fermat number `Fₙ = 2 ^ (2 ^ n) + 1`
is prime if and only if `3 ^ ((Fₙ - 1) / 2) ≡ -1 (mod Fₙ)`.
The `←` direction is `Nat.pepin_primality` from Mathlib. -/
theorem pepin_iff (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fermatNumber n).Prime ↔
      (3 : ZMod (Nat.fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1 :=
  ⟨pepin_of_prime n hn, Nat.pepin_primality n⟩

/-- **Main statement.**  Whether there is a Fermat prime `Fₙ = 2 ^ (2 ^ n) + 1` with index
`n > 4` is a famous open problem (it is widely conjectured that there is none).  What is proved
here is an unconditional *reduction*: such a Fermat prime exists if and only if some `Fₙ` with
`n > 4` passes Pépin's test `3 ^ ((Fₙ - 1) / 2) ≡ -1 (mod Fₙ)`, where `(Fₙ - 1) / 2 = 2 ^ (2 ^ n - 1)`. -/
theorem FermatPrimeBeyondFour :
    (∃ n, 4 < n ∧ (Nat.fermatNumber n).Prime) ↔
      (∃ n, 4 < n ∧ (3 : ZMod (Nat.fermatNumber n)) ^ (2 ^ (2 ^ n - 1)) = -1) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, pepin_of_prime n (by omega) hp⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, Nat.pepin_primality n h⟩

/-! ### Unconditional facts about small Fermat numbers -/

/-- `F₄ = 65537` is prime; in particular there is a Fermat prime whose *value* exceeds `4`. -/
theorem prime_fermatNumber_four : (Nat.fermatNumber 4).Prime := by
  norm_num [Nat.fermatNumber]

/-- There is a Fermat prime greater than `4` (namely `F₄ = 65537`). -/
theorem exists_fermatPrime_gt_four :
    ∃ n, 4 < Nat.fermatNumber n ∧ (Nat.fermatNumber n).Prime :=
  ⟨4, by norm_num [Nat.fermatNumber], prime_fermatNumber_four⟩

/-- `F₅ = 4294967297 = 641 * 6700417` is not prime (Euler). -/
theorem not_prime_fermatNumber_five : ¬ (Nat.fermatNumber 5).Prime := by
  rw [show Nat.fermatNumber 5 = 641 * 6700417 by norm_num [Nat.fermatNumber]]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

end Brockian.FermatNumbers

