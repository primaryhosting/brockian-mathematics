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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to precede every other
command in a file, so the header block above is placed immediately after the
single `import Mathlib` line.

Mathematical content.  The Fermat numbers are `F n = 2 ^ (2 ^ n) + 1`.  The
only known Fermat primes are `F 0, …, F 4` (namely `3, 5, 17, 257, 65537`), and
whether any Fermat prime exists beyond `F 4` is an open problem.  We therefore
prove a Lean-checked *conditional reduction*: the existence of a Fermat prime
`F n` with `n > 4` is equivalent to the existence of `n > 4` satisfying Pépin's
residue condition `3 ^ ((F n - 1) / 2) = -1` in `ZMod (F n)`.  Both directions
of Pépin's test are proved: sufficiency via the Lucas primality criterion, and
necessity via quadratic reciprocity.  We also record that `F 5` and `F 6` are
composite, so the search for a Fermat prime beyond four starts at `n = 7`.
-/

namespace Brockian.FermatNumbers

/-- The `n`-th Fermat number `F n = 2 ^ (2 ^ n) + 1`. -/
def fermat (n : ℕ) : ℕ := 2 ^ 2 ^ n + 1

/-- Pépin's residue condition for the `n`-th Fermat number:
`3 ^ ((F n - 1) / 2) = -1` in `ZMod (F n)`. -/
def PepinResidue (n : ℕ) : Prop := (3 : ZMod (fermat n)) ^ 2 ^ (2 ^ n - 1) = -1

private lemma legendreSym_three_two : legendreSym 3 2 = -1 := by decide

lemma fermat_sub_one (n : ℕ) : fermat n - 1 = 2 ^ 2 ^ n := by
  simp [fermat]

lemma two_pow_split (n : ℕ) : 2 ^ 2 ^ n = 2 * 2 ^ (2 ^ n - 1) := by
  have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [← pow_succ']
  congr 1
  omega

lemma fermat_div_two (n : ℕ) : fermat n / 2 = 2 ^ (2 ^ n - 1) := by
  rw [fermat, two_pow_split n]
  omega

lemma two_lt_fermat (n : ℕ) : 2 < fermat n := by
  have : 2 ^ 1 ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  simp only [fermat]
  omega

lemma fermat_mod_four {n : ℕ} (hn : 1 ≤ n) : fermat n % 4 = 1 := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 2 ^ 2 ^ n = 4 * 2 ^ (2 ^ n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  rw [fermat, h4]
  omega

lemma fermat_mod_three {n : ℕ} (hn : 1 ≤ n) : fermat n % 3 = 2 := by
  have h : 2 ^ 2 ^ n = 4 ^ 2 ^ (n - 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    congr 1
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  have h4 : 4 ^ 2 ^ (n - 1) % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [fermat, Nat.add_mod, h, h4]

/-- Sufficiency in Pépin's test: the residue condition certifies primality.
This is the Lucas primality criterion applied to the base `3`, whose order is
forced to be the full group order `F n - 1 = 2 ^ (2 ^ n)`. -/
theorem prime_of_pepinResidue {n : ℕ} (h : PepinResidue n) : Nat.Prime (fermat n) := by
  haveI : Fact (2 < fermat n) := ⟨two_lt_fermat n⟩
  refine lucas_primality (fermat n) 3 ?_ ?_
  · rw [fermat_sub_one, two_pow_split n, mul_comm, pow_mul, h]
    ring
  · intro q hq hdvd
    rw [fermat_sub_one] at hdvd ⊢
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd)
    subst hq2
    rw [two_pow_split n, Nat.mul_div_cancel_left _ (by norm_num), h]
    exact ZMod.neg_one_ne_one

/-- Necessity in Pépin's test: a Fermat prime `F n` with `n ≥ 1` satisfies the
residue condition, since `3` is a quadratic non-residue mod `F n`
(`F n ≡ 1 [MOD 4]` and `F n ≡ 2 [MOD 3]`, so quadratic reciprocity gives
`legendreSym (F n) 3 = legendreSym 3 2 = -1`). -/
theorem pepinResidue_of_prime {n : ℕ} (hn : 1 ≤ n) (h : Nat.Prime (fermat n)) :
    PepinResidue n := by
  haveI : Fact (Nat.Prime (fermat n)) := ⟨h⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hrec : legendreSym 3 (fermat n) = legendreSym (fermat n) 3 :=
    legendreSym.quadratic_reciprocity_one_mod_four (fermat_mod_four hn) (by norm_num)
  have h3 : legendreSym 3 (fermat n) = -1 := by
    rw [legendreSym.mod]
    have hm : ((fermat n : ℤ) % (3 : ℕ)) = 2 := by
      have := fermat_mod_three hn
      omega
    rw [hm, legendreSym_three_two]
  have hp3 : legendreSym (fermat n) 3 = -1 := by rw [← hrec, h3]
  have hpow := legendreSym.eq_pow (fermat n) 3
  rw [hp3, fermat_div_two] at hpow
  push_cast at hpow
  exact hpow.symm

/-- Pépin's test: for `n ≥ 1`, the Fermat number `F n` is prime if and only if
`3 ^ ((F n - 1) / 2) = -1` in `ZMod (F n)`. -/
theorem prime_iff_pepinResidue {n : ℕ} (hn : 1 ≤ n) :
    Nat.Prime (fermat n) ↔ PepinResidue n :=
  ⟨pepinResidue_of_prime hn, prime_of_pepinResidue⟩

/-- **Fermat Prime Beyond Four** (Lean-checked conditional reduction).
Whether some Fermat number `F n` with `n > 4` is prime is an open problem; here
it is proved equivalent to the existence of some `n > 4` satisfying Pépin's
residue condition. -/
theorem FermatPrimeBeyondFour :
    (∃ n, 4 < n ∧ Nat.Prime (fermat n)) ↔ (∃ n, 4 < n ∧ PepinResidue n) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, pepinResidue_of_prime (by omega) hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, prime_of_pepinResidue hp⟩

/-- The five known Fermat primes: `F 0, F 1, F 2, F 3, F 4` are all prime. -/
theorem prime_fermat_of_le_four {n : ℕ} (hn : n ≤ 4) : Nat.Prime (fermat n) := by
  interval_cases n <;> norm_num [fermat]

/-- `F 5 = 641 * 6700417` is composite. -/
theorem not_prime_fermat_five : ¬ Nat.Prime (fermat 5) := by
  have h : fermat 5 = 641 * 6700417 := by norm_num [fermat]
  rw [h]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- `F 6 = 274177 * 67280421310721` is composite. -/
theorem not_prime_fermat_six : ¬ Nat.Prime (fermat 6) := by
  have h : fermat 6 = 274177 * 67280421310721 := by norm_num [fermat]
  rw [h]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- Consequently, any Fermat prime beyond `F 4` must have index at least `7`. -/
theorem seven_le_of_prime_beyond_four {n : ℕ} (hn : 4 < n) (h : Nat.Prime (fermat n)) :
    7 ≤ n := by
  rcases (by omega : n = 5 ∨ n = 6 ∨ 7 ≤ n) with rfl | rfl | h7
  · exact absurd h not_prime_fermat_five
  · exact absurd h not_prime_fermat_six
  · exact h7

end Brockian.FermatNumbers

