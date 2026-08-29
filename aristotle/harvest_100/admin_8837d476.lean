import Brockian.OreHarmonicNumbers
import Brockian.OreHarmonicNumbersTheory

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

/-!
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Ore harmonic (harmonic divisor) numbers

A positive integer `n` is an *Ore harmonic number* (a harmonic divisor number) when the
harmonic mean of its divisors,

  `H(n) = n * τ(n) / σ(n)`,

is an integer, i.e. when `σ(n) ∣ n * τ(n)`, where `τ(n)` is the number of divisors of `n`
and `σ(n)` is their sum.

The target `OddHarmonicExists` asserts that an *odd* Ore harmonic number exists; it is
witnessed by `n = 1`, for which `H(1) = 1`.

Ore's conjecture — that `1` is the *only* odd harmonic number — is a well-known open problem.
It is recorded (as a `Prop`, not asserted) in the companion file
`Brockian/OreHarmonicNumbersTheory.lean`, together with unconditional partial results towards
it and the identification of the definitions below with Mathlib's `σ` and `τ`.

This file is deliberately import-free (plain core Lean), since the required header comment must
be the very first thing in the file and Lean does not allow a module doc comment before
`import` commands.
-/

namespace Brockian.OreHarmonicNumbers

/-- The list of (positive) divisors of `n`, in increasing order. For `n = 0` this is `[]`. -/
def divisorsList (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => d != 0 && n % d == 0)

/-- `sigmaOne n = σ(n)` is the sum of the positive divisors of `n`. -/
def sigmaOne (n : Nat) : Nat := (divisorsList n).sum

/-- `tau n = τ(n)` is the number of positive divisors of `n`. -/
def tau (n : Nat) : Nat := (divisorsList n).length

/-- `n` is an *Ore harmonic number* (harmonic divisor number) if it is positive and the
harmonic mean `n * τ(n) / σ(n)` of its divisors is an integer. -/
def IsOreHarmonic (n : Nat) : Prop := 0 < n ∧ sigmaOne n ∣ n * tau n

instance (n : Nat) : Decidable (IsOreHarmonic n) :=
  inferInstanceAs (Decidable (0 < n ∧ sigmaOne n ∣ n * tau n))

/-- `n` is odd. (Stated without Mathlib; `isOdd_iff_odd` in the companion file shows this
agrees with Mathlib's `Odd`.) -/
def IsOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-- `1` is odd. -/
theorem isOdd_one : IsOdd 1 := ⟨0, rfl⟩

/-- `1` is an Ore harmonic number: `σ(1) = τ(1) = 1`, so `H(1) = 1`. -/
theorem isOreHarmonic_one : IsOreHarmonic 1 := by decide

/-- **Main target.** There exists an odd Ore harmonic number. -/
theorem OddHarmonicExists : ∃ n : Nat, IsOdd n ∧ IsOreHarmonic n :=
  ⟨1, isOdd_one, isOreHarmonic_one⟩

/-- `6` is an Ore harmonic number, with harmonic mean `H(6) = 6 * 4 / 12 = 2`; it is even. -/
theorem isOreHarmonic_six : IsOreHarmonic 6 := by decide

/-- `28` is an Ore harmonic number, with harmonic mean `H(28) = 28 * 6 / 56 = 3`; it is even. -/
theorem isOreHarmonic_twentyEight : IsOreHarmonic 28 := by decide

/-- `140` is an Ore harmonic number, with harmonic mean `5`; it is even. -/
theorem isOreHarmonic_oneHundredForty : IsOreHarmonic 140 := by decide

end Brockian.OreHarmonicNumbers

import Mathlib
import Brockian.OreHarmonicNumbers

/-!
# Ore harmonic numbers: Mathlib bridge and partial results towards Ore's conjecture

This companion file to `Brockian/OreHarmonicNumbers.lean` (which holds the target theorem
`Brockian.OreHarmonicNumbers.OddHarmonicExists`) identifies the elementary definitions
`sigmaOne`, `tau`, `IsOdd` used there with Mathlib's notions, and proves unconditional
partial results towards **Ore's conjecture**, namely that `1` is the only odd Ore harmonic
number (an open problem, recorded here as `OreConjecture`):

* `not_isOreHarmonic_prime_pow` : no prime power `p ^ k` with `k ≥ 1` is Ore harmonic;
* `one_lt_card_primeFactors_of_isOreHarmonic` : every Ore harmonic number `> 1` has at least
  two distinct prime factors;
* `eq_one_of_odd_of_isOreHarmonic_lt_200` : `1` is the only odd Ore harmonic number `< 200`.
-/

namespace Brockian.OreHarmonicNumbers

open Finset

/-! ### Bridge to Mathlib's `Nat.divisors` -/

theorem nodup_divisorsList (n : ℕ) : (divisorsList n).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

theorem mem_divisorsList {n d : ℕ} : d ∈ divisorsList n ↔ d ∈ n.divisors := by
  simp only [divisorsList, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq, Nat.mem_divisors]
  constructor
  · rintro ⟨hlt, hd0, hmod⟩
    refine ⟨Nat.dvd_of_mod_eq_zero hmod, ?_⟩
    rintro rfl
    omega
  · rintro ⟨hdvd, hn0⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hdvd)
    have hle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    exact ⟨by omega, hd0, Nat.dvd_iff_mod_eq_zero.mp hdvd⟩

theorem toFinset_divisorsList (n : ℕ) : (divisorsList n).toFinset = n.divisors := by
  ext d
  rw [List.mem_toFinset]
  exact mem_divisorsList

theorem sigmaOne_eq (n : ℕ) : sigmaOne n = ∑ d ∈ n.divisors, d := by
  rw [← toFinset_divisorsList, List.sum_toFinset _ (nodup_divisorsList n)]
  simp [sigmaOne]

theorem tau_eq (n : ℕ) : tau n = n.divisors.card := by
  rw [← toFinset_divisorsList, List.toFinset_card_of_nodup (nodup_divisorsList n)]
  rfl

theorem isOdd_iff_odd {n : ℕ} : IsOdd n ↔ Odd n := by
  rw [Nat.odd_iff]
  constructor
  · rintro ⟨k, rfl⟩; omega
  · intro h; exact ⟨n / 2, by omega⟩

/-- The main target restated with Mathlib's `Odd`. -/
theorem oddHarmonicExists_odd : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, odd_one, isOreHarmonic_one⟩

/-- Being Ore harmonic means the harmonic mean of the divisors is a natural number. -/
theorem isOreHarmonic_iff_exists_harmonicMean {n : ℕ} (hn : 0 < n) :
    IsOreHarmonic n ↔ ∃ h : ℕ, n * tau n = sigmaOne n * h := by
  simp [IsOreHarmonic, hn, Dvd.dvd]

/-! ### σ and τ of a prime power -/

theorem sigmaOne_prime_pow {p k : ℕ} (hp : p.Prime) :
    sigmaOne (p ^ k) = ∑ i ∈ range (k + 1), p ^ i := by
  simp [sigmaOne_eq, Nat.sum_divisors_prime_pow hp]

theorem tau_prime_pow {p k : ℕ} (hp : p.Prime) : tau (p ^ k) = k + 1 := by
  simp [tau_eq, Nat.divisors_prime_pow hp]

/-- `σ(p ^ k)` is coprime to `p`. -/
theorem coprime_sigmaOne_prime_pow {p k : ℕ} (hp : p.Prime) :
    Nat.Coprime (sigmaOne (p ^ k)) p := by
  rw [sigmaOne_prime_pow hp, geom_sum_succ]
  have h : p * ∑ i ∈ range k, p ^ i + 1 = 1 + p * ∑ i ∈ range k, p ^ i := by ring
  rw [h, Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left p

/-- For `k ≥ 1` we have `σ(p ^ k) > τ(p ^ k) = k + 1`. -/
theorem tau_lt_sigmaOne_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    tau (p ^ k) < sigmaOne (p ^ k) := by
  rw [tau_prime_pow hp, sigmaOne_prime_pow hp]
  have key : ∑ _i ∈ range (k + 1), 1 < ∑ i ∈ range (k + 1), p ^ i := by
    refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ hp.pos) ⟨1, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · simpa using hp.one_lt
  simpa using key

/-! ### No prime power `> 1` is harmonic -/

/-- No prime power `p ^ k` with `k ≥ 1` is an Ore harmonic number. -/
theorem not_isOreHarmonic_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ¬ IsOreHarmonic (p ^ k) := by
  rintro ⟨-, hdvd⟩
  have hcop : Nat.Coprime (sigmaOne (p ^ k)) (p ^ k) :=
    Nat.Coprime.pow_right _ (coprime_sigmaOne_prime_pow hp)
  have hdvd' : sigmaOne (p ^ k) ∣ tau (p ^ k) := hcop.dvd_of_dvd_mul_left hdvd
  have hpos : 0 < tau (p ^ k) := by rw [tau_prime_pow hp]; omega
  exact absurd (Nat.le_of_dvd hpos hdvd') (not_le.mpr (tau_lt_sigmaOne_prime_pow hp hk))

/-- Every Ore harmonic number `> 1` has at least two distinct prime factors. In particular
this applies to any counterexample to Ore's conjecture. -/
theorem one_lt_card_primeFactors_of_isOreHarmonic {n : ℕ} (hn : 1 < n)
    (h : IsOreHarmonic n) : 1 < n.primeFactors.card := by
  rcases Nat.lt_or_ge n.primeFactors.card 2 with hcard | hcard
  · interval_cases hc : n.primeFactors.card
    · exact absurd (Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hc)) (by omega)
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
      have hpp : p.Prime :=
        Nat.prime_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
      have hne : n ≠ 0 := by omega
      have hfac : n = p ^ n.factorization p := by
        conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hne]
        rw [Nat.prod_factorization_eq_prod_primeFactors, hp]
        simp
      have hk : 1 ≤ n.factorization p := by
        rcases Nat.eq_zero_or_pos (n.factorization p) with h0 | h0
        · rw [h0, pow_zero] at hfac; omega
        · omega
      exact absurd (hfac ▸ h) (not_isOreHarmonic_prime_pow hpp hk)
  · omega

/-! ### Ore's conjecture -/

/-- **Ore's conjecture** (open): `1` is the only odd Ore harmonic number. -/
def OreConjecture : Prop := ∀ n : ℕ, Odd n → IsOreHarmonic n → n = 1

set_option maxRecDepth 100000 in
/-- Unconditional finite verification: `1` is the only odd Ore harmonic number below `200`. -/
theorem eq_one_of_odd_of_isOreHarmonic_lt_200 :
    ∀ n < 200, n % 2 = 1 → IsOreHarmonic n → n = 1 := by decide

/-- Ore's conjecture is equivalent to the nonexistence of an odd Ore harmonic number `> 1`. -/
theorem oreConjecture_iff :
    OreConjecture ↔ ¬ ∃ n : ℕ, 1 < n ∧ Odd n ∧ IsOreHarmonic n := by
  constructor
  · rintro hc ⟨n, hn, hodd, h⟩
    exact absurd (hc n hodd h) (by omega)
  · intro hc n hodd h
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact absurd h.1 (by omega)
      · omega
    · exact absurd ⟨n, by omega, hodd, h⟩ hc

end Brockian.OreHarmonicNumbers

