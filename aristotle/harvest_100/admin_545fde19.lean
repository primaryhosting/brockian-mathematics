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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` are *betrothed* (quasi-amicable) numbers: they are distinct and each one's
sum of divisors equals `m + n + 1`. -/
def Betrothed (m n : ℕ) : Prop :=
  m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- A betrothed pair whose two members have the same parity. -/
def SameParityBetrothed (m n : ℕ) : Prop :=
  Betrothed m n ∧ m % 2 = n % 2

/-- `n` is either a perfect square or twice a perfect square. -/
def SquareOrTwiceSquare (n : ℕ) : Prop :=
  ∃ a : ℕ, n = a ^ 2 ∨ n = 2 * a ^ 2

/-- Parity of a geometric-type sum with odd ratio. -/
lemma geom_sum_mod_two_of_odd {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ i ∈ range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
    omega

/-- A number all of whose prime exponents are even is a square. -/
lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  have key : ∀ p ∈ n.primeFactors, p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2)
      = p ^ (n.factorization p) := by
    intro p _
    rw [← pow_add]
    congr 1
    obtain ⟨c, hc⟩ := h p
    omega
  rw [Finset.prod_congr rfl key]
  exact (Nat.factorization_prod_pow_eq_self hn).symm.trans
    (Nat.prod_factorization_eq_prod_primeFactors _)

/-- For an odd number, an odd sum of divisors forces the number to be a square. -/
lemma isSquare_of_odd_sigma_of_odd {m : ℕ} (hm : Odd m) (h : Odd (σ 1 m)) : IsSquare m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  refine isSquare_of_factorization_even hm0 ?_
  intro p
  by_cases hp : p ∈ m.primeFactors
  · have hprod := sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hm0
    have hdvd : (∑ i ∈ range (m.factorization p + 1), p ^ (i * 1)) ∣ σ 1 m := by
      rw [hprod]; exact Finset.dvd_prod_of_mem _ hp
    have hodd : Odd (∑ i ∈ range (m.factorization p + 1), p ^ (i * 1)) := h.of_dvd_nat hdvd
    have hpodd : Odd p := by
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      rcases hpp.eq_two_or_odd' with h2 | h2
      · exact absurd (h2 ▸ hpm) (by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using hm)
      · exact h2
    have hgs := geom_sum_mod_two_of_odd hpodd (m.factorization p + 1)
    simp only [mul_one] at hodd
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  · simp [Finsupp.notMem_support_iff.mp hp]

/-- If `σ n` is odd, then `n` is a square or twice a square. -/
lemma squareOrTwiceSquare_of_odd_sigma {n : ℕ} (hn : n ≠ 0) (h : Odd (σ 1 n)) :
    SquareOrTwiceSquare n := by
  obtain ⟨k, m, hmodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hmodd)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop] at h
  have hsm : Odd (σ 1 m) := h.of_dvd_nat (Dvd.intro_left _ rfl)
  obtain ⟨a, ha⟩ := isSquare_of_odd_sigma_of_odd hmodd hsm
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨2 ^ j * a, Or.inl (by subst hj ha; ring)⟩
  · exact ⟨2 ^ j * a, Or.inr (by subst hj ha; ring)⟩

/-- A member of a betrothed pair is nonzero. -/
lemma Betrothed.ne_zero_left {m n : ℕ} (h : Betrothed m n) : m ≠ 0 := by
  rintro rfl
  have := h.2.1
  simp at this

/-- A member of a betrothed pair is nonzero. -/
lemma Betrothed.ne_zero_right {m n : ℕ} (h : Betrothed m n) : n ≠ 0 := by
  rintro rfl
  have := h.2.2
  simp at this

/--
**Betrothed numbers of equal parity.**

It is a longstanding open question (Brockian problem) whether a betrothed
(quasi-amicable) pair `m ≠ n` with `σ m = σ n = m + n + 1` can have both members of the
same parity; every known pair has opposite parity.

We prove a Lean-checked reduction: such a pair exists if and only if one exists whose two
members are each a perfect square or twice a perfect square.  Indeed, for a same-parity pair
`m + n + 1` is odd, so `σ m` and `σ n` are odd, which forces this structure.
-/
theorem SameParityBetrothedExists :
    (∃ m n : ℕ, SameParityBetrothed m n) ↔
      (∃ m n : ℕ, SameParityBetrothed m n ∧ SquareOrTwiceSquare m ∧ SquareOrTwiceSquare n) := by
  constructor
  · rintro ⟨m, n, hb, hpar⟩
    have hodd : Odd (m + n + 1) := by
      rcases Nat.even_or_odd m with hm | hm
      · have hn : Even n := by
          rw [Nat.even_iff] at hm ⊢; omega
        exact (hm.add hn).add_one
      · have hn : Odd n := by
          rw [Nat.odd_iff] at hm ⊢; omega
        exact (hm.add_odd hn).add_one
    refine ⟨m, n, ⟨hb, hpar⟩, ?_, ?_⟩
    · exact squareOrTwiceSquare_of_odd_sigma hb.ne_zero_left (hb.2.1 ▸ hodd)
    · exact squareOrTwiceSquare_of_odd_sigma hb.ne_zero_right (hb.2.2 ▸ hodd)
  · rintro ⟨m, n, h, -, -⟩
    exact ⟨m, n, h⟩

end Brockian.BetrothedNumbers

