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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`. Whether an odd superperfect
number exists is an open problem, so the target result
`Brockian.SuperperfectNumbers.OddSuperperfectExists` is a Lean-checked *conditional
reduction*: the existence of an odd superperfect number is equivalent to the existence of
one satisfying a list of proved necessary conditions (size lower bound from a kernel
computation, deficiency bounds, non-divisibility by `3` in the non-square case, and parity
information in the square case).
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is *superperfect* when `σ(σ(n)) = 2n` (and `n > 0`). -/
def Superperfect (n : ℕ) : Prop := 0 < n ∧ sigma (sigma n) = 2 * n

@[simp] lemma sigma_zero : sigma 0 = 0 := by simp [sigma]

@[simp] lemma sigma_one : sigma 1 = 1 := by simp [sigma]

lemma sigma_eq_properDivisors_add (n : ℕ) :
    sigma n = (∑ d ∈ n.properDivisors, d) + n := by
  simpa [sigma] using Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)

/-- If `N` factors as `a * b` with both factors `> 1`, then `1`, `b`, `N` are three distinct
divisors of `N`, so `σ(N) ≥ N + b + 1`. -/
lemma add_add_one_le_sigma {N a b : ℕ} (hN : N = a * b) (ha : 1 < a) (hb : 1 < b) :
    N + b + 1 ≤ sigma N := by
  have hNb : b < N := by
    subst hN; nlinarith
  have hsub : ({1, b} : Finset ℕ) ⊆ N.properDivisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_properDivisors.mpr ⟨one_dvd _, by omega⟩
    · exact Nat.mem_properDivisors.mpr ⟨⟨a, by rw [hN]; ring⟩, hNb⟩
  have hsum : ∑ d ∈ ({1, b} : Finset ℕ), d = 1 + b := by
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ b)]
  have h2 : 1 + b ≤ ∑ d ∈ N.properDivisors, d :=
    hsum ▸ Finset.sum_le_sum_of_subset (f := fun d : ℕ => d) hsub
  rw [sigma_eq_properDivisors_add]
  omega

lemma self_lt_sigma {n : ℕ} (hn : 1 < n) : n < sigma n := by
  have hsub : ({1} : Finset ℕ) ⊆ n.properDivisors := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact Nat.mem_properDivisors.mpr ⟨one_dvd _, hn⟩
  have h2 : 1 ≤ ∑ d ∈ n.properDivisors, d := by
    have := Finset.sum_le_sum_of_subset (f := fun d : ℕ => d) hsub
    simpa using this
  rw [sigma_eq_properDivisors_add]
  omega

lemma sigma_pos {n : ℕ} (hn : 0 < n) : 0 < sigma n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    simp
  · exact lt_trans hn (self_lt_sigma h)

lemma Superperfect.one_lt {n : ℕ} (h : Superperfect n) : 1 < n := by
  rcases h with ⟨hpos, heq⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp at heq
  · exact hn

/-- A superperfect number is deficient: `σ(n) < 2n`. -/
lemma Superperfect.sigma_lt {n : ℕ} (h : Superperfect n) : sigma n < 2 * n := by
  by_contra hcon
  push_neg at hcon
  have h1 : 1 < sigma n := lt_of_lt_of_le (by have := h.one_lt; omega) hcon
  have := self_lt_sigma h1
  rw [h.2] at this
  omega

lemma Superperfect.self_lt_sigma {n : ℕ} (h : Superperfect n) : n < sigma n :=
  _root_.Brockian.SuperperfectNumbers.self_lt_sigma h.one_lt

/-- If `n` is superperfect and `σ(n)` is even, then `n` is strongly deficient:
`3σ(n) + 2 ≤ 4n`. -/
theorem sigma_bound_of_even_sigma {n : ℕ} (h : Superperfect n) (he : Even (sigma n)) :
    3 * sigma n + 2 ≤ 4 * n := by
  obtain ⟨k, hk⟩ := he
  have hn : 1 < n := h.one_lt
  have hlt : n < sigma n := h.self_lt_sigma
  have hk2 : sigma n = 2 * k := by omega
  have hk1 : 1 < k := by omega
  have := add_add_one_le_sigma (N := sigma n) (a := 2) (b := k) hk2 (by norm_num) hk1
  rw [h.2] at this
  omega

/-- An odd superperfect number with even `σ` is not divisible by `3`. -/
theorem not_three_dvd_of_even_sigma {n : ℕ} (hodd : Odd n) (h : Superperfect n)
    (he : Even (sigma n)) : ¬ (3 ∣ n) := by
  rintro ⟨k, hk⟩
  have hn : 1 < n := h.one_lt
  have hbound := sigma_bound_of_even_sigma h he
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- `n = 3` (`k = 0` and `k = 1` are excluded by `1 < n`)
    interval_cases k
    · omega
    · -- n = 3, σ(3) = 4, σ(4) = 7 ≠ 6
      have h3 : n = 3 := by omega
      subst h3
      have : sigma 3 = 4 := by decide
      have h4 : sigma (sigma 3) = 7 := by rw [this]; decide
      have := h.2
      omega
  · have := add_add_one_le_sigma (N := n) (a := 3) (b := k) hk (by norm_num) hk2
    omega

/-- The parity of a sum of odd numbers is the parity of the number of summands. -/
lemma sum_mod_two_eq_card_mod_two {s : Finset ℕ} (h : ∀ d ∈ s, Odd d) :
    (∑ d ∈ s, d) % 2 = s.card % 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : a % 2 = 1 := Nat.odd_iff.mp (h a (by simp))
      have h2 := ih fun d hd => h d (by simp [hd])
      omega

/-- A positive natural number is a perfect square iff all exponents in its prime
factorisation are even. -/
lemma isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩
    intro p
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp only [Finsupp.coe_add, Pi.add_apply]
    exact ⟨_, rfl⟩
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := h p
    omega

/-- A positive natural number has an odd number of divisors iff it is a perfect square. -/
lemma odd_card_divisors_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    Odd n.divisors.card ↔ IsSquare n := by
  rw [isSquare_iff_even_factorization hn, Nat.card_divisors hn, Nat.not_even_iff_odd.symm,
    even_iff_two_dvd, (Nat.prime_two.prime).dvd_finset_prod_iff]
  constructor
  · intro h p
    by_cases hp : p ∈ n.primeFactors
    · have h2 : ¬ (2 ∣ (n.factorization p + 1)) := fun hd => h ⟨p, hp, hd⟩
      rcases Nat.even_or_odd (n.factorization p) with he | ho
      · exact he
      · exact absurd (by rcases ho with ⟨k, hk⟩; omega : 2 ∣ (n.factorization p + 1)) h2
    · have h0 : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.notMem_support_iff.mp hp
      simp [h0]
  · rintro h ⟨p, _, hd⟩
    obtain ⟨k, hk⟩ := h p
    omega

/-- For odd `n`, `σ(n)` is odd exactly when `n` is a perfect square. -/
theorem odd_sigma_iff_isSquare {n : ℕ} (hpos : 0 < n) (hodd : Odd n) :
    Odd (sigma n) ↔ IsSquare n := by
  have hn : n ≠ 0 := hpos.ne'
  have hpar : sigma n % 2 = n.divisors.card % 2 := by
    refine sum_mod_two_eq_card_mod_two fun d hd => ?_
    exact Odd.of_dvd_nat hodd (Nat.mem_divisors.mp hd).1
  rw [← odd_card_divisors_iff_isSquare hn, Nat.odd_iff, Nat.odd_iff, hpar]

/-- **Kanold-type partial result.** An odd superperfect number divisible by `3`
must be a perfect square. -/
theorem isSquare_of_three_dvd {n : ℕ} (hodd : Odd n) (h : Superperfect n) (h3 : 3 ∣ n) :
    IsSquare n := by
  by_contra hsq
  have he : Even (sigma n) := by
    rcases Nat.even_or_odd (sigma n) with he | ho
    · exact he
    · exact absurd ((odd_sigma_iff_isSquare h.1 hodd).mp ho) hsq
  exact not_three_dvd_of_even_sigma hodd h he h3

/-- If an odd superperfect number is a perfect square, then `σ(n)` is odd and is itself
not a perfect square. -/
theorem odd_sigma_and_sigma_not_isSquare_of_isSquare {n : ℕ} (hodd : Odd n)
    (h : Superperfect n) (hsq : IsSquare n) : Odd (sigma n) ∧ ¬ IsSquare (sigma n) := by
  have hs : Odd (sigma n) := (odd_sigma_iff_isSquare h.1 hodd).mpr hsq
  refine ⟨hs, fun hsq' => ?_⟩
  have hpos : 0 < sigma n := sigma_pos h.1
  have : Odd (sigma (sigma n)) := (odd_sigma_iff_isSquare hpos hs).mpr hsq'
  rw [h.2] at this
  exact (Nat.not_odd_iff_even.mpr ⟨n, by ring⟩) this

/-! ### A verified finite search

A direct kernel computation shows that there is no odd superperfect number below `1000`.
(The literature records a far larger verified bound; the point here is that the bound below
is checked by the Lean kernel.) -/

section FiniteCheck

set_option maxRecDepth 1000000

private lemma check_lt_250 :
    ∀ n ∈ Finset.Ico 0 250, n % 2 = 1 → sigma (sigma n) ≠ 2 * n := by decide

set_option maxHeartbeats 1000000 in
private lemma check_lt_500 :
    ∀ n ∈ Finset.Ico 250 500, n % 2 = 1 → sigma (sigma n) ≠ 2 * n := by decide

set_option maxHeartbeats 1000000 in
private lemma check_lt_750 :
    ∀ n ∈ Finset.Ico 500 750, n % 2 = 1 → sigma (sigma n) ≠ 2 * n := by decide

set_option maxHeartbeats 2000000 in
private lemma check_lt_1000 :
    ∀ n ∈ Finset.Ico 750 1000, n % 2 = 1 → sigma (sigma n) ≠ 2 * n := by decide

/-- There is no odd superperfect number below `1000`. -/
theorem not_superperfect_of_odd_of_lt_1000 {n : ℕ} (hodd : Odd n) (hn : n < 1000) :
    ¬ Superperfect n := by
  rintro ⟨-, heq⟩
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  rcases Nat.lt_or_ge n 250 with h | h
  · exact check_lt_250 n (Finset.mem_Ico.mpr ⟨Nat.zero_le _, h⟩) h2 heq
  rcases Nat.lt_or_ge n 500 with h' | h'
  · exact check_lt_500 n (Finset.mem_Ico.mpr ⟨h, h'⟩) h2 heq
  rcases Nat.lt_or_ge n 750 with h'' | h''
  · exact check_lt_750 n (Finset.mem_Ico.mpr ⟨h', h''⟩) h2 heq
  · exact check_lt_1000 n (Finset.mem_Ico.mpr ⟨h'', hn⟩) h2 heq

end FiniteCheck

/-- **Conditional reduction for the existence of an odd superperfect number.**

An odd superperfect number exists if and only if there is one satisfying all of the
following necessary conditions: it is at least `1000`, it is deficient (`n < σ(n) < 2n`),
and unless it is a perfect square it is strongly deficient (`3σ(n) + 2 ≤ 4n`) and not
divisible by `3`; while if it is a perfect square, `σ(n)` is odd and is not a square. -/
theorem OddSuperperfectExists :
    (∃ n : ℕ, Odd n ∧ Superperfect n) ↔
      ∃ n : ℕ, Odd n ∧ 1000 ≤ n ∧ Superperfect n ∧ n < sigma n ∧ sigma n < 2 * n ∧
        (¬ IsSquare n → 3 * sigma n + 2 ≤ 4 * n ∧ ¬ (3 ∣ n)) ∧
        (IsSquare n → Odd (sigma n) ∧ ¬ IsSquare (sigma n)) := by
  constructor
  · rintro ⟨n, hodd, h⟩
    have hbig : 1000 ≤ n := by
      by_contra hlt
      exact not_superperfect_of_odd_of_lt_1000 hodd (by omega) h
    refine ⟨n, hodd, hbig, h, h.self_lt_sigma, h.sigma_lt, fun hsq => ?_,
      fun hsq => odd_sigma_and_sigma_not_isSquare_of_isSquare hodd h hsq⟩
    have he : Even (sigma n) := by
      rcases Nat.even_or_odd (sigma n) with he | ho
      · exact he
      · exact absurd ((odd_sigma_iff_isSquare h.1 hodd).mp ho) hsq
    exact ⟨sigma_bound_of_even_sigma h he, not_three_dvd_of_even_sigma hodd h he⟩
  · rintro ⟨n, hodd, -, h, -⟩
    exact ⟨n, hodd, h⟩

end Brockian.SuperperfectNumbers

