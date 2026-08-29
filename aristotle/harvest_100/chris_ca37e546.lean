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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every other command, so the header above is a plain
-- comment; it is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Summary

A *Giuga number* is a composite `n` with `p ∣ n / p - 1` for every prime `p ∣ n`
(`IsGiuga`).  The smallest one is `30`.  Whether an **odd** Giuga number exists is an open
problem, so the target `OddGiugaExists` is stated and proved here as a Lean-checked
equivalent reformulation (a reduction), not as an unconditional existence claim:

* `OddGiugaExists` : an odd Giuga number exists **iff** there is a finite set `S` of at least
  two odd primes with `p ∣ (∏ q ∈ S \ {p}, q) - 1` for every `p ∈ S`.

Supporting results and unconditional partial results proved here:

* `IsGiuga.squarefree` : Giuga numbers are squarefree;
* `isGiugaSet_primeFactors` / `isGiuga_prod` : the two directions of the reduction;
* `isGiuga_30` : `30` is a Giuga number;
* `IsGiuga.dvd_sum_div_sub_one` : Giuga's congruence `n ∣ (∑ p ∈ n.primeFactors, n / p) - 1`;
* `IsGiuga.one_lt_sum_inv` : the reciprocals of the prime factors sum to more than `1`;
* `odd_giuga_nine_le_card` : an odd Giuga number has at least nine distinct prime factors.
-/

open scoped BigOperators

namespace Brockian.GiugaNumbers

/-- `n` is a *Giuga number* if it is composite (`1 < n` and not prime) and for every prime
divisor `p` of `n` we have `p ∣ n / p - 1`. -/
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

/-- A finite set `S` of at least two primes is a *Giuga set* if for every `p ∈ S`,
`p` divides `(∏ q ∈ S \ {p}, q) - 1`.  Giuga sets are exactly the sets of prime factors of
Giuga numbers (see `isGiugaSet_primeFactors` and `isGiuga_prod`). -/
def IsGiugaSet (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, p.Prime) ∧ 2 ≤ S.card ∧ ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1

/-- Every Giuga number is squarefree. -/
theorem IsGiuga.squarefree {n : ℕ} (hn : IsGiuga n) : Squarefree n := by
  obtain ⟨h1, -, hdvd⟩ := hn
  rw [Nat.squarefree_iff_prime_squarefree]
  rintro p hp ⟨k, hk⟩
  have hpn : p ∣ n := ⟨p * k, by rw [hk]; ring⟩
  have hdiv : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have h2 : p ∣ n / p := ⟨k, hdiv⟩
  have h3 : p ∣ n / p - 1 := hdvd p hp hpn
  have hpos : 1 ≤ n / p := Nat.one_le_div_iff hp.pos |>.mpr (Nat.le_of_dvd (by omega) hpn)
  have h4 := Nat.dvd_sub h2 h3
  rw [show n / p - (n / p - 1) = 1 from by omega] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

/-- For a squarefree `n` and a prime factor `p`, `n / p` is the product of the other prime
factors. -/
theorem div_eq_prod_erase {n p : ℕ} (hs : Squarefree n) (hp : p ∈ n.primeFactors) :
    n / p = ∏ q ∈ n.primeFactors.erase p, q := by
  have hfac : ∏ q ∈ n.primeFactors, q = n := Nat.prod_primeFactors_of_squarefree hs
  have hsplit : p * ∏ q ∈ n.primeFactors.erase p, q = n := by
    rw [Finset.mul_prod_erase _ (fun q => q) hp, hfac]
  have hppos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  calc n / p = (p * ∏ q ∈ n.primeFactors.erase p, q) / p := by rw [hsplit]
    _ = ∏ q ∈ n.primeFactors.erase p, q := Nat.mul_div_cancel_left _ hppos

/-- The set of prime factors of a Giuga number is a Giuga set. -/
theorem isGiugaSet_primeFactors {n : ℕ} (hn : IsGiuga n) : IsGiugaSet n.primeFactors := by
  have hsq : Squarefree n := hn.squarefree
  obtain ⟨h1, hnp, hdvd⟩ := hn
  refine ⟨fun p hp => Nat.prime_of_mem_primeFactors hp, ?_, ?_⟩
  · by_contra hcard
    push_neg at hcard
    interval_cases h : n.primeFactors.card
    · have : n.primeFactors = ∅ := Finset.card_eq_zero.mp h
      obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
      have : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, by omega⟩
      simp_all
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
      have hfac : ∏ q ∈ n.primeFactors, q = n := Nat.prod_primeFactors_of_squarefree hsq
      rw [hp, Finset.prod_singleton] at hfac
      have hpmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
      exact hnp (hfac ▸ Nat.prime_of_mem_primeFactors hpmem)
  · intro p hp
    rw [← div_eq_prod_erase hsq hp]
    exact hdvd p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- The product of a Giuga set is a Giuga number. -/
theorem isGiuga_prod {S : Finset ℕ} (hS : IsGiugaSet S) : IsGiuga (∏ q ∈ S, q) := by
  obtain ⟨hprimes, hcard, hcond⟩ := hS
  set n : ℕ := ∏ q ∈ S, q with hn
  have hpos : 0 < n := Finset.prod_pos fun q hq => (hprimes q hq).pos
  obtain ⟨p, hpS⟩ : ∃ p, p ∈ S := Finset.card_pos.mp (by omega)
  have hpp : p.Prime := hprimes p hpS
  have hsplit : p * ∏ q ∈ S.erase p, q = n := Finset.mul_prod_erase _ (fun q => q) hpS
  have herase : ∃ r, r ∈ S.erase p := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_erase_of_mem hpS]
    omega
  obtain ⟨r, hr⟩ := herase
  have hrp : r.Prime := hprimes r (Finset.mem_of_mem_erase hr)
  have hprodpos : 0 < ∏ q ∈ S.erase p, q :=
    Finset.prod_pos fun q hq => (hprimes q (Finset.mem_of_mem_erase hq)).pos
  have hge : 2 ≤ ∏ q ∈ S.erase p, q :=
    le_trans hrp.two_le (Nat.le_of_dvd hprodpos (Finset.dvd_prod_of_mem _ hr))
  have hpn : p ∣ n := ⟨_, hsplit.symm⟩
  have hlt : p < n := by
    calc p = p * 1 := by ring
    _ < p * ∏ q ∈ S.erase p, q := by
        have := hpp.pos; nlinarith
    _ = n := hsplit
  refine ⟨by nlinarith [hpp.two_le], ?_, ?_⟩
  · intro hnp
    rcases (Nat.Prime.eq_one_or_self_of_dvd hnp p hpn) with h | h
    · exact hpp.one_lt.ne' h
    · omega
  · intro q hq hqn
    have hqS : q ∈ S := by
      have : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, by omega⟩
      rwa [hn, Nat.primeFactors_prod hprimes] at this
    have hqsplit : q * ∏ x ∈ S.erase q, x = n := Finset.mul_prod_erase _ (fun x => x) hqS
    have hdq : n / q = ∏ x ∈ S.erase q, x := by
      rw [← hqsplit, Nat.mul_div_cancel_left _ hq.pos]
    rw [hdq]
    exact hcond q hqS

/-- **Reduction of the odd Giuga problem to Giuga sets of odd primes.**

An odd Giuga number exists if and only if there is a finite set of at least two *odd* primes
`S` such that each `p ∈ S` divides `(∏ q ∈ S \ {p}, q) - 1`.

Whether either side holds is an open problem; this theorem is a Lean-checked reduction. -/
theorem OddGiugaExists :
    (∃ n : ℕ, Odd n ∧ IsGiuga n) ↔
      (∃ S : Finset ℕ, IsGiugaSet S ∧ ∀ p ∈ S, Odd p) := by
  constructor
  · rintro ⟨n, hodd, hn⟩
    refine ⟨n.primeFactors, isGiugaSet_primeFactors hn, ?_⟩
    intro p hp
    rw [Nat.odd_iff]
    by_contra hpar
    have hp2 : 2 ∣ p := by omega
    have : 2 ∣ n := hp2.trans (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.odd_iff] at hodd
    omega
  · rintro ⟨S, hS, hodd⟩
    refine ⟨∏ q ∈ S, q, ?_, isGiuga_prod hS⟩
    rw [Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    intro h2
    obtain ⟨p, hpS, hp2⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff (fun q => q)).mp h2
    have := hodd p hpS
    rw [Nat.odd_iff] at this
    omega

/-- `30 = 2 * 3 * 5` is a Giuga number. -/
theorem isGiuga_30 : IsGiuga 30 := by
  have hS : IsGiugaSet ({2, 3, 5} : Finset ℕ) := by
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have h := isGiuga_prod hS
  have hprod : (∏ q ∈ ({2, 3, 5} : Finset ℕ), q) = 30 := by decide
  rwa [hprod] at h

/-!
## Partial results towards the odd Giuga problem
-/

/-- Every prime factor of a Giuga number `n` divides `(∑ q ∈ n.primeFactors, n / q) - 1`. -/
theorem IsGiuga.prime_dvd_sum_sub_one {n p : ℕ} (hn : IsGiuga n) (hp : p ∈ n.primeFactors) :
    p ∣ (∑ q ∈ n.primeFactors, n / q) - 1 := by
  have hsq := hn.squarefree
  obtain ⟨h1, hnp, hdvd⟩ := hn
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have hge : 1 ≤ n / p := (Nat.one_le_div_iff hpp.pos).mpr (Nat.le_of_dvd (by omega) hpn)
  have hA : p ∣ n / p - 1 := hdvd p hpp hpn
  have hB : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q := by
    refine Finset.dvd_sum ?_
    intro q hq
    have hqmem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
    have hne : q ≠ p := Finset.ne_of_mem_erase hq
    rw [div_eq_prod_erase hsq hqmem]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hp⟩)
  have hsum : n / p + ∑ q ∈ n.primeFactors.erase p, n / q = ∑ q ∈ n.primeFactors, n / q :=
    Finset.add_sum_erase _ _ hp
  have key : (∑ q ∈ n.primeFactors, n / q) - 1
      = (n / p - 1) + ∑ q ∈ n.primeFactors.erase p, n / q := by omega
  rw [key]
  exact hA.add hB

/-- **Giuga's congruence.** A Giuga number `n` divides `(∑ p ∈ n.primeFactors, n / p) - 1`. -/
theorem IsGiuga.dvd_sum_div_sub_one {n : ℕ} (hn : IsGiuga n) :
    n ∣ (∑ p ∈ n.primeFactors, n / p) - 1 := by
  have hfac : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hn.squarefree
  have h := Finset.prod_primes_dvd (s := n.primeFactors) ((∑ p ∈ n.primeFactors, n / p) - 1)
    (fun a ha => (Nat.prime_of_mem_primeFactors ha).prime)
    (fun a ha => hn.prime_dvd_sum_sub_one ha)
  rwa [hfac] at h

/-- For a Giuga number, the sum of the reciprocals of its prime factors exceeds `1`. -/
theorem IsGiuga.one_lt_sum_inv {n : ℕ} (hn : IsGiuga n) :
    1 < ∑ p ∈ n.primeFactors, (1 : ℚ) / p := by
  obtain ⟨hprimes, hcard, -⟩ := isGiugaSet_primeFactors hn
  have hn1 : 1 < n := hn.1
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < n.primeFactors.card)
  have hqp : q.Prime := hprimes q hq
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq
  have hdivpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqn) hqp.pos
  have hpdvd : p ∣ n / q := by
    rw [div_eq_prod_erase hn.squarefree hq]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hpq, hp⟩)
  have hterm : 2 ≤ n / q := le_trans (hprimes p hp).two_le (Nat.le_of_dvd hdivpos hpdvd)
  have hle : n / q ≤ ∑ r ∈ n.primeFactors, n / r :=
    Finset.single_le_sum (f := fun r => n / r) (fun i _ => Nat.zero_le _) hq
  have hlt : n < ∑ r ∈ n.primeFactors, n / r := by
    have := Nat.le_of_dvd (by omega) hn.dvd_sum_div_sub_one
    omega
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : (n : ℚ) < ∑ r ∈ n.primeFactors, (n : ℚ) / r := by
    have h1 : (n : ℚ) < ((∑ r ∈ n.primeFactors, n / r : ℕ) : ℚ) := by exact_mod_cast hlt
    have h2 : ((∑ r ∈ n.primeFactors, n / r : ℕ) : ℚ) = ∑ r ∈ n.primeFactors, (n : ℚ) / r := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      exact Nat.cast_div (Nat.dvd_of_mem_primeFactors hr)
        (Nat.cast_ne_zero.mpr (hprimes r hr).ne_zero)
    rwa [h2] at h1
  have hrw : ∑ r ∈ n.primeFactors, (n : ℚ) / r
      = (n : ℚ) * ∑ r ∈ n.primeFactors, (1 : ℚ) / r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hrw] at hcast
  nlinarith [hcast, hnpos]

/-- A lower bound for the `i`-th smallest odd prime (exact for `i < 8`). -/
def oddPrimeLB : ℕ → ℕ
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | 4 => 13
  | 5 => 17
  | 6 => 19
  | _ => 23

theorem three_le_oddPrimeLB (i : ℕ) : 3 ≤ oddPrimeLB i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => simp [oddPrimeLB]
  | (n + 7) => simp [oddPrimeLB]

/-- A set of `k ≤ 8` distinct odd primes has reciprocal sum at most the sum of the reciprocals
of the `k` smallest odd primes. -/
theorem sum_inv_le_prime_bound :
    ∀ (k : ℕ), k ≤ 8 → ∀ S : Finset ℕ, S.card = k → (∀ x ∈ S, x.Prime) → (∀ x ∈ S, Odd x) →
      ∑ x ∈ S, (1 : ℚ) / x ≤ ∑ i ∈ Finset.range k, (1 : ℚ) / (oddPrimeLB i) := by
  intro k
  induction k with
  | zero =>
    intro _ S hS _ _
    rw [Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro hk8 S hS hprime hodd
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hM : S.max' hne ∈ S := S.max'_mem hne
    set M := S.max' hne with hMdef
    have hMprime := hprime M hM
    have hModd : M % 2 = 1 := by have := hodd M hM; rwa [Nat.odd_iff] at this
    have hM3 : 3 ≤ M := by have := hMprime.two_le; omega
    have hPS : ∀ x ∈ S, 3 ≤ x ∧ x % 2 = 1 ∧ (x = 3 ∨ x % 3 ≠ 0) := by
      intro x hx
      have h2 := (hprime x hx).two_le
      have hox : x % 2 = 1 := by have := hodd x hx; rwa [Nat.odd_iff] at this
      refine ⟨by omega, hox, ?_⟩
      by_cases h : x % 3 = 0
      · left
        have hdvd : (3 : ℕ) ∣ x := Nat.dvd_of_mod_eq_zero h
        exact (((hprime x hx).eq_one_or_self_of_dvd 3 hdvd).resolve_left (by norm_num)).symm
      · right; exact h
    -- counting the admissible values below a bound
    have hcards : ∀ j < 8, ((Finset.range (oddPrimeLB j)).filter
        (fun x => 3 ≤ x ∧ x % 2 = 1 ∧ (x = 3 ∨ x % 3 ≠ 0))).card = j := by decide
    have hbound : oddPrimeLB k ≤ M := by
      by_contra hlt
      push_neg at hlt
      have hsub : S ⊆ (Finset.range (oddPrimeLB k)).filter
          (fun x => 3 ≤ x ∧ x % 2 = 1 ∧ (x = 3 ∨ x % 3 ≠ 0)) := by
        intro x hx
        have hxM : x ≤ M := S.le_max' x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hPS x hx⟩
      have hcle := Finset.card_le_card hsub
      have hk : k < 8 := by omega
      rw [hcards k hk] at hcle
      omega
    have hcard' : (S.erase M).card = k := by
      rw [Finset.card_erase_of_mem hM, hS]
      omega
    have h1 := ih (by omega) (S.erase M) hcard'
      (fun x hx => hprime x (Finset.mem_of_mem_erase hx))
      (fun x hx => hodd x (Finset.mem_of_mem_erase hx))
    have hsum : ∑ x ∈ S, (1 : ℚ) / x
        = 1 / (M : ℚ) + ∑ x ∈ S.erase M, (1 : ℚ) / x :=
      (Finset.add_sum_erase _ (fun x : ℕ => (1 : ℚ) / (x : ℚ)) hM).symm
    have hLBpos : (0 : ℚ) < (oddPrimeLB k : ℚ) := by
      have h3 : (3 : ℚ) ≤ (oddPrimeLB k : ℚ) := by exact_mod_cast three_le_oddPrimeLB k
      linarith
    have hMcast : ((oddPrimeLB k : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hbound
    have hterm : (1 : ℚ) / M ≤ 1 / (oddPrimeLB k : ℚ) :=
      one_div_le_one_div_of_le hLBpos hMcast
    rw [Finset.sum_range_succ, hsum]
    linarith

/-- The reciprocals of the eight smallest odd primes sum to less than `1`. -/
theorem prime_bound_eight_lt_one : ∑ i ∈ Finset.range 8, (1 : ℚ) / (oddPrimeLB i) < 1 := by
  norm_num [Finset.sum_range_succ, oddPrimeLB]

/-- **Partial result.** An odd Giuga number must have at least nine distinct prime factors. -/
theorem odd_giuga_nine_le_card {n : ℕ} (hodd : Odd n) (hn : IsGiuga n) :
    9 ≤ n.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hoddp : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    rw [Nat.odd_iff]
    by_contra hpar
    have hp2 : 2 ∣ p := by omega
    have h2n : 2 ∣ n := hp2.trans (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.odd_iff] at hodd
    omega
  have h1 := hn.one_lt_sum_inv
  have hbound := sum_inv_le_prime_bound n.primeFactors.card (by omega) n.primeFactors rfl
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hoddp
  have hsub : Finset.range n.primeFactors.card ⊆ Finset.range 8 :=
    Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
  have hmono : ∑ i ∈ Finset.range n.primeFactors.card, (1 : ℚ) / (oddPrimeLB i)
      ≤ ∑ i ∈ Finset.range 8, (1 : ℚ) / (oddPrimeLB i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have := prime_bound_eight_lt_one
  linarith

end Brockian.GiugaNumbers

