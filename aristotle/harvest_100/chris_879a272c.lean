/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
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

namespace Brockian

/-! ### A kernel-friendly primality test

Mathlib's `Nat.decidablePrime` instance tests every candidate divisor below `n`, which makes
`by decide` too slow for a few hundred numbers of size ~1300.  We therefore use trial division by
the divisors `d` with `d * d ≤ n`, together with the correctness lemma `isPrimeB_prime`. -/

/-- `trialDivB n k = true` iff no `d ≤ k` with `2 ≤ d` and `d * d ≤ n` divides `n`. -/
def trialDivB (n : ℕ) : ℕ → Bool
  | 0 => true
  | (k + 1) =>
      (!(decide (2 ≤ k + 1) && decide ((k + 1) * (k + 1) ≤ n) && decide (n % (k + 1) = 0)))
        && trialDivB n k

lemma trialDivB_spec (n : ℕ) : ∀ (k d : ℕ), trialDivB n k = true → 2 ≤ d → d ≤ k →
    d * d ≤ n → ¬ (d ∣ n) := by
  intro k
  induction k with
  | zero => intro d _ _ hd; omega
  | succ k ih =>
      intro d h h2 hd hdd
      rw [trialDivB, Bool.and_eq_true] at h
      obtain ⟨h1, h3⟩ := h
      rcases Nat.lt_or_ge d (k + 1) with hlt | hge
      · exact ih d h3 h2 (by omega) hdd
      · have hk : d = k + 1 := by omega
        subst hk
        intro hdvd
        simp [h2, hdd] at h1
        exact h1 (Nat.dvd_iff_mod_eq_zero.mp hdvd)

/-- Boolean primality test, correct for all `n ≤ 36 ^ 2 + 36 = 1368`. -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && trialDivB n 36

lemma isPrimeB_prime {n : ℕ} (hn : n ≤ 1368) (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, ht⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  have hm36 : m ≤ 36 := by nlinarith
  exact trialDivB_spec n 36 m ht hm hm36 hmm

/-! ### The wheel search -/

/-- The spokes of the wheel: the primes below `100`, used as candidate small summands. -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- The smallest spoke `p` of the wheel such that both `p` and `n - p` are prime
(and `0` if there is none). -/
def gwit (n : ℕ) : ℕ := ((smallPrimes.find? (fun p => isPrimeB p && isPrimeB (n - p)))).getD 0

lemma gwit_le (n : ℕ) : gwit n ≤ 97 := by
  unfold gwit
  cases h : smallPrimes.find? (fun p => isPrimeB p && isPrimeB (n - p)) with
  | none => simp
  | some p =>
      have hmem : p ∈ smallPrimes := List.mem_of_find?_eq_some h
      simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hmem
      simp only [Option.getD_some]
      omega

/-- The exhaustive check: every even `n` with `4 ≤ n ≤ 2 * 631` has a Goldbach witness among the
spokes of the wheel. -/
def gcheck : Bool :=
  (List.range 630).all (fun i =>
    isPrimeB (gwit (2 * i + 4)) && isPrimeB (2 * i + 4 - gwit (2 * i + 4)) &&
      decide (gwit (2 * i + 4) < 2 * i + 4))

lemma gcheck_true : gcheck = true := by decide

/-- **Goldbach wheel, `K = 2`, modulus `631`.**  Every even number `n` with
`4 ≤ n ≤ 2 * 631 = 1262` is a sum of two primes.  (`K = 2`: two prime summands; the wheel
modulus `631` fixes the verified range `2 * 631`.) -/
theorem GoldbachWheelK2_631 (n : ℕ) (hn : Even n) (h4 : 4 ≤ n) (hle : n ≤ 2 * 631) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  obtain ⟨m, hm⟩ := hn
  set i : ℕ := (n - 4) / 2 with hi
  have hni : 2 * i + 4 = n := by omega
  have hilt : i < 630 := by omega
  have hall := List.all_eq_true.mp gcheck_true i (List.mem_range.mpr hilt)
  rw [hni] at hall
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨hp, hq⟩, hlt⟩ := hall
  refine ⟨gwit n, n - gwit n, ?_, ?_, by omega⟩
  · exact isPrimeB_prime (le_trans (gwit_le n) (by norm_num)) hp
  · exact isPrimeB_prime (by omega) hq

end Brockian

