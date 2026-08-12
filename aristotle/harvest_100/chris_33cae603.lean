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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Harmonic Exists

An *Ore harmonic number* (harmonic divisor number) is a positive integer `n` for which the
harmonic mean of the divisors of `n`, namely `n * τ n / σ n`, is an integer.  Ore's conjecture
states that `1` is the only odd harmonic number; here we prove that an odd harmonic number
does exist (namely `1`), that it is the only one below `1000`, and record the basic
characterisation of the definition in terms of the harmonic mean.
-/

namespace Brockian.OreHarmonicNumbers

open Finset

/-- The sum of the divisors of `n`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- The number of divisors of `n`. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- `n` is an *Ore harmonic number* (harmonic divisor number) if `n` is positive and the
harmonic mean of its divisors, namely `n * τ n / σ n`, is a natural number. -/
def IsOreHarmonic (n : ℕ) : Prop := 0 < n ∧ sigmaOne n ∣ n * tau n

instance : DecidablePred IsOreHarmonic := fun n => by
  unfold IsOreHarmonic; infer_instance

/-- The harmonic mean of the divisors of `n`, as a rational number. -/
def harmonicMean (n : ℕ) : ℚ := (n : ℚ) * (tau n : ℚ) / (sigmaOne n : ℚ)

lemma sigmaOne_pos {n : ℕ} (hn : 0 < n) : 0 < sigmaOne n := by
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
  exact Finset.sum_pos' (by intro i _; exact Nat.zero_le i) ⟨1, h1, Nat.one_pos⟩

/-- `harmonicMean n` really is the harmonic mean of the divisors of `n`, i.e. the number of
divisors divided by the sum of their reciprocals. -/
lemma harmonicMean_eq {n : ℕ} (hn : 0 < n) :
    harmonicMean n = (tau n : ℚ) / (∑ d ∈ n.divisors, (1 : ℚ) / d) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : (sigmaOne n : ℚ) ≠ 0 := by exact_mod_cast (sigmaOne_pos hn).ne'
  have key : (∑ d ∈ n.divisors, (1 : ℚ) / d) * n = (sigmaOne n : ℚ) := by
    rw [Finset.sum_mul]
    have hcongr : ∀ d ∈ n.divisors, (1 : ℚ) / d * n = ((n / d : ℕ) : ℚ) := by
      intro d hd
      obtain ⟨hdvd, hn'⟩ := Nat.mem_divisors.mp hd
      have hd0 : (d : ℚ) ≠ 0 := by
        have : d ≠ 0 := by rintro rfl; exact hn' (zero_dvd_iff.mp hdvd)
        exact_mod_cast this
      rw [Nat.cast_div hdvd hd0]
      field_simp
    rw [Finset.sum_congr rfl hcongr, ← Nat.cast_sum]
    exact_mod_cast Nat.sum_div_divisors n (fun x => x)
  have hsum : (∑ d ∈ n.divisors, (1 : ℚ) / d) = (sigmaOne n : ℚ) / n := by
    rw [eq_div_iff hn0]; exact key
  rw [hsum, harmonicMean]
  field_simp

/-- `n` is Ore harmonic exactly when the harmonic mean of its divisors is a natural number. -/
lemma isOreHarmonic_iff {n : ℕ} (hn : 0 < n) :
    IsOreHarmonic n ↔ ∃ k : ℕ, harmonicMean n = (k : ℚ) := by
  have hs : (sigmaOne n : ℚ) ≠ 0 := by exact_mod_cast (sigmaOne_pos hn).ne'
  constructor
  · rintro ⟨-, c, hc⟩
    refine ⟨c, ?_⟩
    rw [harmonicMean, div_eq_iff hs]
    have := congrArg (fun x : ℕ => (x : ℚ)) hc
    push_cast at this
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨hn, k, ?_⟩
    rw [harmonicMean, div_eq_iff hs] at hk
    have : ((n * tau n : ℕ) : ℚ) = ((sigmaOne n * k : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this

/-- **Main result.** There exists an odd Ore harmonic number. -/
theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, ⟨0, by norm_num⟩, by decide⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
/-- `1` is the only odd Ore harmonic number below `1000`
(Ore's conjecture asserts that it is the only one at all). -/
theorem odd_harmonic_below_1000_eq_one :
    ∀ n < 1000, Odd n → IsOreHarmonic n → n = 1 := by decide

/-! ### No prime power is harmonic -/

lemma tau_prime_pow {p a : ℕ} (hp : p.Prime) : tau (p ^ a) = a + 1 := by
  simp [tau, Nat.divisors_prime_pow hp]

lemma sigmaOne_prime_pow {p a : ℕ} (hp : p.Prime) :
    sigmaOne (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
  simpa [sigmaOne] using Nat.sum_divisors_prime_pow (f := fun x => x) hp

lemma geom_sum_eq_one_add_mul (p a : ℕ) :
    ∃ k, ∑ i ∈ Finset.range (a + 1), p ^ i = 1 + p * k := by
  induction a with
  | zero => exact ⟨0, by simp⟩
  | succ a ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + p ^ a, by rw [Finset.sum_range_succ, hk]; ring⟩

lemma coprime_sigmaOne_prime_pow {p a : ℕ} (hp : p.Prime) :
    Nat.Coprime (sigmaOne (p ^ a)) (p ^ a) := by
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, sigmaOne_prime_pow hp]
  obtain ⟨k, hk⟩ := geom_sum_eq_one_add_mul p a
  rw [hk]
  intro hdvd
  have h1 : p ∣ 1 := (Nat.dvd_add_right ⟨k, rfl⟩).mp (by simpa [Nat.add_comm] using hdvd)
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

lemma lt_sigmaOne_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    a + 1 < sigmaOne (p ^ a) := by
  rw [sigmaOne_prime_pow hp]
  have h : ∑ _i ∈ Finset.range (a + 1), 1 < ∑ i ∈ Finset.range (a + 1), p ^ i := by
    refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ hp.pos) ⟨1, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · simpa using hp.one_lt
  simpa using h

/-- No prime power `p ^ a` with `a ≥ 1` is an Ore harmonic number. -/
theorem not_isOreHarmonic_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ¬ IsOreHarmonic (p ^ a) := by
  rintro ⟨-, hdvd⟩
  rw [tau_prime_pow hp] at hdvd
  have h1 : sigmaOne (p ^ a) ∣ a + 1 :=
    Nat.Coprime.dvd_of_dvd_mul_left (coprime_sigmaOne_prime_pow hp) hdvd
  have h2 : sigmaOne (p ^ a) ≤ a + 1 := Nat.le_of_dvd (by omega) h1
  exact absurd h2 (not_le.mpr (lt_sigmaOne_prime_pow hp ha))

/-- An Ore harmonic number is never a prime power; in particular every Ore harmonic number
`> 1` has at least two distinct prime factors. -/
theorem not_isPrimePow_of_isOreHarmonic {n : ℕ} (h : IsOreHarmonic n) : ¬ IsPrimePow n := by
  rintro ⟨p, k, hp, hk, rfl⟩
  exact not_isOreHarmonic_prime_pow (Nat.prime_iff.mpr hp) hk h

/-- A parity constraint: for odd `n`, the sum of the divisors and the number of divisors have
the same parity. -/
theorem sigmaOne_mod_two_eq_tau_mod_two {n : ℕ} (hn : Odd n) :
    sigmaOne n % 2 = tau n % 2 := by
  have hodd : ∀ d ∈ n.divisors, d % 2 = 1 := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.odd_iff.mp (Odd.of_dvd_nat hn hdvd)
  rw [sigmaOne, Finset.sum_nat_mod, Finset.sum_congr rfl hodd]
  simp [tau]

end Brockian.OreHarmonicNumbers

