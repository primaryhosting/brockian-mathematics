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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` whose sums of prime
factors, counted with multiplicity, agree; the name comes from the pair `(714, 715)`.
Whether there are infinitely many such pairs is an open problem (Erdős); the file below
develops the basic theory of the function `sopfr`, proves a number of unconditional
structural results about Ruth–Aaron pairs, and gives the infinitude statement as a
conditional reduction from the unboundedness hypothesis.
-/

namespace Brockian
namespace RuthAaronPairs

/-! ## The sum-of-prime-factors function `sopfr` -/

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(OEIS A001414).  By convention `sopfr 0 = sopfr 1 = 0`. -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- A *Ruth–Aaron pair* is a pair of consecutive integers `n`, `n + 1` (with `n ≥ 2`)
having the same sum of prime factors, counted with multiplicity. -/
def IsRuthAaronPair (n : ℕ) : Prop := 2 ≤ n ∧ sopfr n = sopfr (n + 1)

@[simp] lemma sopfr_zero : sopfr 0 = 0 := by simp [sopfr]

@[simp] lemma sopfr_one : sopfr 1 = 0 := by simp [sopfr]

lemma sopfr_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

lemma sopfr_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sopfr (a * b) = sopfr a + sopfr b := by
  simp [sopfr, (Nat.perm_primeFactorsList_mul ha hb).sum_eq]

private lemma list_sum_le_prod :
    ∀ L : List ℕ, (∀ x ∈ L, 2 ≤ x) → L.sum ≤ L.prod ∧ (L ≠ [] → 2 ≤ L.prod)
  | [], _ => by simp
  | a :: L, h => by
      have hL : ∀ x ∈ L, 2 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have ih := list_sum_le_prod L hL
      have ha : 2 ≤ a := h a (List.mem_cons_self ..)
      rcases eq_or_ne L [] with rfl | hne
      · simp
        omega
      · have h2 := ih.2 hne
        have h1 := ih.1
        simp only [List.sum_cons, List.prod_cons]
        exact ⟨by nlinarith, fun _ => by nlinarith⟩

/-- The sum of the prime factors of `n` never exceeds `n`. -/
lemma sopfr_le_self (n : ℕ) : sopfr n ≤ n := by
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · have hp := Nat.prod_primeFactorsList h0
    have := (list_sum_le_prod (Nat.primeFactorsList n)
      (fun x hx => (Nat.prime_of_mem_primeFactorsList hx).two_le)).1
    simpa [sopfr, hp] using this

/-- If `n` is even and at least `8`, then `sopfr n < n - 1`. -/
lemma sopfr_lt_of_even {n : ℕ} (hn : 8 ≤ n) (h2 : 2 ∣ n) : sopfr n < n - 1 := by
  obtain ⟨m, rfl⟩ := h2
  have h : sopfr (2 * m) = 2 + sopfr m := by
    rw [sopfr_mul (by norm_num) (by omega), sopfr_prime (by norm_num)]
  have hle := sopfr_le_self m
  omega

/-- `sopfr` of a product of a list of primes is the sum of that list. -/
lemma sopfr_list_prod : ∀ L : List ℕ, (∀ p ∈ L, p.Prime) → sopfr L.prod = L.sum
  | [], _ => by simp
  | a :: L, h => by
      have ha : a.Prime := h a (List.mem_cons_self ..)
      have hL : ∀ p ∈ L, p.Prime := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hprod : L.prod ≠ 0 := by
        rcases eq_or_ne L [] with rfl | hne
        · simp
        · have := (list_sum_le_prod L (fun x hx => (hL x hx).two_le)).2 hne
          omega
      simp only [List.prod_cons, List.sum_cons]
      rw [sopfr_mul ha.ne_zero hprod, sopfr_prime ha, sopfr_list_prod L hL]

/-- Convenient computation rule: if `n` is the product of the list of primes `L`,
then `sopfr n` is the sum of `L`. -/
lemma sopfr_eq_sum_of_prod {n : ℕ} (L : List ℕ) (hL : ∀ p ∈ L, p.Prime) (h : L.prod = n) :
    sopfr n = L.sum := h ▸ sopfr_list_prod L hL

/-! ## Explicit Ruth–Aaron pairs -/

lemma ruthAaron_5 : IsRuthAaronPair 5 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_sum_of_prod [5] (by norm_num) (by norm_num),
    sopfr_eq_sum_of_prod [2, 3] (by norm_num) (by norm_num)]
  norm_num

lemma ruthAaron_8 : IsRuthAaronPair 8 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_sum_of_prod [2, 2, 2] (by norm_num) (by norm_num),
    sopfr_eq_sum_of_prod [3, 3] (by norm_num) (by norm_num)]
  norm_num

lemma ruthAaron_15 : IsRuthAaronPair 15 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_sum_of_prod [3, 5] (by norm_num) (by norm_num),
    sopfr_eq_sum_of_prod [2, 2, 2, 2] (by norm_num) (by norm_num)]
  norm_num

lemma ruthAaron_77 : IsRuthAaronPair 77 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_sum_of_prod [7, 11] (by norm_num) (by norm_num),
    sopfr_eq_sum_of_prod [2, 3, 13] (by norm_num) (by norm_num)]
  norm_num

lemma ruthAaron_125 : IsRuthAaronPair 125 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_sum_of_prod [5, 5, 5] (by norm_num) (by norm_num),
    sopfr_eq_sum_of_prod [2, 3, 3, 7] (by norm_num) (by norm_num)]
  norm_num

/-- The eponymous pair: `714 = 2·3·7·17` and `715 = 5·11·13`, both with `sopfr = 29`. -/
lemma ruthAaron_714 : IsRuthAaronPair 714 := by
  refine ⟨by norm_num, ?_⟩
  rw [sopfr_eq_sum_of_prod [2, 3, 7, 17] (by norm_num) (by norm_num),
    sopfr_eq_sum_of_prod [5, 11, 13] (by norm_num) (by norm_num)]
  norm_num

/-! ## Unconditional structural results -/

/-- There are no three consecutive primes. -/
lemma no_three_consecutive_primes {p : ℕ} (hp : p.Prime) (h1 : (p + 1).Prime)
    (h2 : (p + 2).Prime) : False := by
  rcases Nat.even_or_odd p with he | ho
  · have hp2 : p = 2 := (Nat.Prime.even_iff hp).mp he
    subst hp2
    norm_num at h2
  · have he1 : Even (p + 1) := by
      rcases ho with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have h3 : p + 1 = 2 := (Nat.Prime.even_iff h1).mp he1
    have h4 : p = 1 := by omega
    subst h4
    norm_num at hp

/-- If `n` is prime and `n ≥ 7`, then `(n, n+1)` is not a Ruth–Aaron pair: indeed
`sopfr (n+1) < sopfr n`. -/
lemma sopfr_succ_lt_of_prime {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : sopfr (p + 1) < sopfr p := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2 : 2 ∣ p + 1 := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have := sopfr_lt_of_even (n := p + 1) (by omega) h2
  rw [sopfr_prime hp]
  omega

/-- If `n + 1` is prime then `sopfr n < sopfr (n+1)`, so `(n, n+1)` is not a Ruth–Aaron pair. -/
lemma sopfr_lt_of_succ_prime {n : ℕ} (hp : (n + 1).Prime) : sopfr n < sopfr (n + 1) := by
  have := sopfr_le_self n
  rw [sopfr_prime hp]
  omega

/-- Neither member of a Ruth–Aaron pair `(n, n+1)` with `n ≥ 7` is prime. -/
theorem not_prime_of_ruthAaron {n : ℕ} (h : IsRuthAaronPair n) (hn : 7 ≤ n) :
    ¬ n.Prime ∧ ¬ (n + 1).Prime := by
  obtain ⟨-, heq⟩ := h
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have := sopfr_succ_lt_of_prime hp hn
    omega
  · have := sopfr_lt_of_succ_prime (n := n) hp
    omega

/-- **No Ruth–Aaron pair of semiprimes.**  There are no primes `p, q, r` and an integer `s`
with `p * q + 1 = r * s` and `p + q = r + s`.  In particular no Ruth–Aaron pair `(n, n+1)`
has both `n` and `n + 1` a product of exactly two primes. -/
theorem no_semiprime_ruthAaronPair {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hprod : p * q + 1 = r * s) (hsum : p + q = r + s) : False := by
  have hprod' : (p : ℤ) * q + 1 = r * s := by exact_mod_cast hprod
  have hsum' : (p : ℤ) + q = r + s := by exact_mod_cast hsum
  -- The key identity `(r - p) * (r - q) = -1`.
  have key : ((r : ℤ) - p) * ((r : ℤ) - q) = -1 := by
    linear_combination hprod' - (r : ℤ) * hsum'
  have hcases : ((r : ℤ) - p = 1 ∧ (r : ℤ) - q = -1) ∨ ((r : ℤ) - p = -1 ∧ (r : ℤ) - q = 1) := by
    have h1 : ((r : ℤ) - p) ∣ 1 := ⟨-((r : ℤ) - q), by linarith [key]⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one h1) with h | h
    · exact Or.inl ⟨h, by rw [h] at key; linarith⟩
    · exact Or.inr ⟨h, by rw [h] at key; linarith⟩
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hp1 : p + 1 = r := by omega
    have hq1 : q = r + 1 := by omega
    subst hq1; subst hp1
    exact no_three_consecutive_primes hp hr hq
  · have hp1 : p = r + 1 := by omega
    have hq1 : q + 1 = r := by omega
    subst hp1; subst hq1
    exact no_three_consecutive_primes hq hr hp

/-- Restatement of `no_semiprime_ruthAaronPair` for Ruth–Aaron pairs: if `n = p * q` and
`n + 1 = r * s` with `p, q, r, s` prime, then `(n, n+1)` is not a Ruth–Aaron pair. -/
theorem not_ruthAaron_of_semiprimes {n p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hn : n = p * q) (hn1 : n + 1 = r * s) :
    ¬ IsRuthAaronPair n := by
  rintro ⟨-, heq⟩
  subst hn
  rw [hn1, sopfr_mul hp.ne_zero hq.ne_zero, sopfr_mul hr.ne_zero hs.ne_zero,
    sopfr_prime hp, sopfr_prime hq, sopfr_prime hr, sopfr_prime hs] at heq
  exact no_semiprime_ruthAaronPair hp hq hr (by omega) heq

/-! ## Sign changes of `sopfr (n+1) - sopfr n` -/

/-- `sopfr n < sopfr (n+1)` happens infinitely often (take `n = p - 1` for `p` prime). -/
theorem infinite_sopfr_lt_succ : {n : ℕ | sopfr n < sopfr (n + 1)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 2)
  have hp1 : p - 1 + 1 = p := by have := hp.two_le; omega
  exact ⟨p - 1, sopfr_lt_of_succ_prime (n := p - 1) (by rwa [hp1]), by omega⟩

/-- `sopfr (n+1) < sopfr n` happens infinitely often (take `n = p` for `p` prime). -/
theorem infinite_sopfr_succ_lt : {n : ℕ | sopfr (n + 1) < sopfr n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max (N + 1) 7)
  have h7 : 7 ≤ p := le_trans (le_max_right _ _) hpN
  have hN : N < p := lt_of_lt_of_le (Nat.lt_succ_self N) (le_trans (le_max_left _ _) hpN)
  exact ⟨p, sopfr_succ_lt_of_prime hp h7, hN⟩

/-- Consequently the difference `sopfr (n+1) - sopfr n` changes sign infinitely often:
for every prime `p ≥ 7` one has `sopfr (p-1) < sopfr p` and `sopfr (p+1) < sopfr p`. -/
theorem infinitely_many_sign_changes :
    {n : ℕ | sopfr n < sopfr (n + 1) ∧ sopfr (n + 2) < sopfr (n + 1)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max (N + 2) 7)
  have h7 : 7 ≤ p := le_trans (le_max_right _ _) hpN
  have hN : N + 2 ≤ p := le_trans (le_max_left _ _) hpN
  have hp1 : p - 1 + 1 = p := by omega
  have hp2 : p - 1 + 2 = p + 1 := by omega
  refine ⟨p - 1, ⟨sopfr_lt_of_succ_prime (n := p - 1) (by rwa [hp1]), ?_⟩, by omega⟩
  rw [hp1, hp2]
  exact sopfr_succ_lt_of_prime hp h7

/-! ## Infinitude -/

/-- The Ruth–Aaron unboundedness hypothesis: there are Ruth–Aaron pairs beyond every bound.
This is the (open) conjecture of Erdős that Ruth–Aaron pairs never stop occurring. -/
def RuthAaronUnbounded : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsRuthAaronPair n

/-- **Ruth–Aaron infinitude (conditional reduction).**  Granting the unboundedness
hypothesis `RuthAaronUnbounded` — i.e. that Ruth–Aaron pairs occur beyond every bound —
the set of Ruth–Aaron pairs is infinite.

The infinitude of Ruth–Aaron pairs is an open problem, so the statement is given here in
conditional form; the converse implication is `ruthAaronUnbounded_of_infinite`, so the
hypothesis is exactly equivalent to the conclusion. -/
theorem RuthAaronInfinitude (H : RuthAaronUnbounded) :
    {n : ℕ | IsRuthAaronPair n}.Infinite :=
  Set.infinite_of_forall_exists_gt fun N => by
    obtain ⟨n, hn, hpair⟩ := H N
    exact ⟨n, hpair, hn⟩

/-- Converse of `RuthAaronInfinitude`. -/
theorem ruthAaronUnbounded_of_infinite (H : {n : ℕ | IsRuthAaronPair n}.Infinite) :
    RuthAaronUnbounded := fun N => by
  obtain ⟨n, hn, hlt⟩ := H.exists_gt N
  exact ⟨n, hlt, hn⟩

/-- The infinitude of Ruth–Aaron pairs is equivalent to their unboundedness. -/
theorem ruthAaron_infinite_iff_unbounded :
    {n : ℕ | IsRuthAaronPair n}.Infinite ↔ RuthAaronUnbounded :=
  ⟨ruthAaronUnbounded_of_infinite, RuthAaronInfinitude⟩

end RuthAaronPairs
end Brockian

