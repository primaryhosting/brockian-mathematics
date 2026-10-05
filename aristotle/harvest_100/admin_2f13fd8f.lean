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
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.OreHarmonicNumbers

/-- The sum of the divisors of `n`, usually written `σ n`. -/
def divisorSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- The number of divisors of `n`, usually written `τ n`. -/
def numDivisors (n : ℕ) : ℕ := n.divisors.card

/-- `n` is an *Ore harmonic number* (harmonic divisor number) if the harmonic mean
`n * τ n / σ n` of its divisors is an integer, i.e. if `σ n ∣ n * τ n`. -/
def IsOreHarmonic (n : ℕ) : Prop :=
  0 < n ∧ divisorSum n ∣ n * numDivisors n

/-- Equivalent reformulation: the harmonic mean of the divisors of `n` is an integer. -/
theorem isOreHarmonic_iff (n : ℕ) :
    IsOreHarmonic n ↔ 0 < n ∧ ∃ H : ℕ, n * numDivisors n = divisorSum n * H := by
  simp [IsOreHarmonic, Dvd.dvd]

/-- **Odd harmonic exists**: there is an odd Ore harmonic number, namely `n = 1`
(whose divisors have harmonic mean `1`). -/
theorem OddHarmonicExists : ∃ n : ℕ, Odd n ∧ IsOreHarmonic n :=
  ⟨1, odd_one, Nat.one_pos, by simp [divisorSum, numDivisors]⟩

/-- `6` is an (even) Ore harmonic number: its divisors have harmonic mean `2`. -/
theorem isOreHarmonic_six : IsOreHarmonic 6 :=
  ⟨by norm_num, by decide⟩

/-- `28` is an (even) Ore harmonic number: its divisors have harmonic mean `3`. -/
theorem isOreHarmonic_twentyEight : IsOreHarmonic 28 :=
  ⟨by norm_num, by decide⟩

section PrimePow

variable {p k : ℕ}

/-- The sum of divisors of a prime power. -/
theorem divisorSum_primePow (hp : p.Prime) (k : ℕ) :
    divisorSum (p ^ k) = ∑ i ∈ range (k + 1), p ^ i := by
  simpa [divisorSum] using Nat.sum_divisors_prime_pow (f := fun d => d) hp

/-- The number of divisors of a prime power. -/
theorem numDivisors_primePow (hp : p.Prime) (k : ℕ) :
    numDivisors (p ^ k) = k + 1 := by
  have h : ((p ^ k).divisors.card : ℕ) = ∑ _d ∈ (p ^ k).divisors, 1 := by
    simp
  rw [numDivisors, h, Nat.sum_divisors_prime_pow (f := fun _ => (1 : ℕ)) hp]
  simp

/-- The sum of divisors of `p ^ k` is coprime to `p`. -/
theorem coprime_divisorSum_primePow (hp : p.Prime) (k : ℕ) :
    Nat.Coprime (divisorSum (p ^ k)) p := by
  have hsplit : (∑ i ∈ range (k + 1), p ^ i)
      = 1 + (∑ i ∈ range k, p ^ i) * p := by
    rw [Finset.sum_range_succ']
    simp [Finset.sum_mul, pow_succ, Nat.add_comm]
  rw [divisorSum_primePow hp, hsplit]
  simp

/-- The sum of divisors of `p ^ k` is at least `1 + p ^ k`. -/
theorem le_divisorSum_primePow (hp : p.Prime) (hk : 0 < k) :
    1 + p ^ k ≤ divisorSum (p ^ k) := by
  rw [divisorSum_primePow hp]
  have hsub : ({0, k} : Finset ℕ) ⊆ range (k + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  have hne : (0 : ℕ) ≠ k := by omega
  have h := Finset.sum_le_sum_of_subset (f := fun i => p ^ i) hsub
  simpa [Finset.sum_pair hne] using h

/-- No prime power `p ^ k` with `k ≥ 1` is an Ore harmonic number.  In particular an odd
Ore harmonic number greater than `1` cannot be a power of a single prime. -/
theorem not_isOreHarmonic_primePow (hp : p.Prime) (hk : 0 < k) :
    ¬ IsOreHarmonic (p ^ k) := by
  rintro ⟨-, hdvd⟩
  rw [numDivisors_primePow hp] at hdvd
  have hcop : Nat.Coprime (divisorSum (p ^ k)) (p ^ k) :=
    (coprime_divisorSum_primePow hp k).pow_right k
  have hdvd' : divisorSum (p ^ k) ∣ (k + 1) := hcop.dvd_of_dvd_mul_left hdvd
  have hle : divisorSum (p ^ k) ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdvd'
  have hge : 1 + p ^ k ≤ divisorSum (p ^ k) := le_divisorSum_primePow hp hk
  have hlt : k < p ^ k := Nat.lt_pow_self hp.one_lt
  omega

/-- An odd Ore harmonic number greater than `1` is not a prime power. -/
theorem odd_isOreHarmonic_not_primePow {n : ℕ} (hharm : IsOreHarmonic n) :
    ¬ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k := by
  rintro ⟨p, k, hp, hk, rfl⟩
  exact not_isOreHarmonic_primePow hp hk hharm

end PrimePow

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
/-- Verified partial case of Ore's conjecture: there is no odd Ore harmonic number `n`
with `2 ≤ n ≤ 1000`. -/
theorem no_odd_isOreHarmonic_le_1000 :
    ∀ n ∈ Finset.Icc 2 1000, Odd n → ¬ IsOreHarmonic n := by
  have key : ∀ n ∈ Finset.Icc 2 1000, Odd n →
      ¬ ((∑ d ∈ Nat.divisors n, d) ∣ n * (Nat.divisors n).card) := by decide
  intro n hn hodd h
  exact key n hn hodd h.2

end Brockian.OreHarmonicNumbers

