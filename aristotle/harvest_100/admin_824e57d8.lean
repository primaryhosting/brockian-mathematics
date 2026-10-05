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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires every `import` to precede any module docstring, so the required header is
reproduced verbatim as the module docstring immediately after the import below.)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

De Polignac's conjecture states that for every positive even number `n` there are infinitely
many pairs of *consecutive* primes whose difference is `n`.  This is an open problem (it contains
the twin prime conjecture as the case `n = 2`), so what is proved here is a *conditional
reduction*: the full conjecture is derived from a two-form special case of Dickson's conjecture
on prime values of linear forms (`DicksonPairHypothesis`).

The reduction is the classical sieve-free argument: given an even `n ≥ 2`, one uses the Chinese
remainder theorem to build an arithmetic progression `r + M ℕ` such that

* every `p ≡ r [MOD M]` has `p + k` divisible by a fixed prime `< p` for each `0 < k < n`
  (so all the numbers strictly between `p` and `p + n` are composite), and
* the pair of linear forms `r + M m`, `r + n + M m` is admissible, i.e. no prime divides
  the product for all `m`.

Dickson's conjecture applied to this pair then produces infinitely many consecutive prime pairs
with gap exactly `n`.

Unconditional results proved here as well:

* `Brockian.PolignacPrimes.eq_two_of_odd_gap` – for odd `n` at most one prime `p` has `p + n`
  prime, so the evenness hypothesis in the conjecture is necessary;
* `Brockian.PolignacPrimes.not_polignacProperty_of_odd`;
* `Brockian.PolignacPrimes.polignacProperty_iff` – reformulation of the "infinitely many"
  clause as an unboundedness statement.
-/

namespace Brockian.PolignacPrimes

/-- `p` and `p + n` are consecutive primes: both are prime and no number strictly between
them is prime. -/
def IsPrimeGap (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + n) ∧ ∀ q : ℕ, p < q → q < p + n → ¬ Nat.Prime q

/-- De Polignac's property for a number `n`: there are infinitely many pairs of consecutive
primes with difference exactly `n`. -/
def PolignacProperty (n : ℕ) : Prop := {p : ℕ | IsPrimeGap n p}.Infinite

/-- The two-form special case of **Dickson's conjecture** that is used as the hypothesis of the
reduction: if the two linear forms `m ↦ r + M m` and `m ↦ r + n + M m` are admissible (for every
prime `q` some `m` makes both values indivisible by `q`), then both forms are simultaneously
prime for arbitrarily large `m`. -/
def DicksonPairHypothesis : Prop :=
  ∀ r M n : ℕ, 0 < M → 0 < n →
    (∀ q : ℕ, Nat.Prime q → ∃ m : ℕ, ¬ q ∣ (r + M * m) ∧ ¬ q ∣ (r + n + M * m)) →
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ Nat.Prime (r + M * m) ∧ Nat.Prime (r + n + M * m)

/-! ### Elementary reformulations -/

lemma infinite_of_unbounded {S : Set ℕ} (h : ∀ N : ℕ, ∃ p ∈ S, N < p) : S.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hlt⟩ := h N
  exact absurd (hN hp) (by omega)

/-- `PolignacProperty n` says exactly that consecutive prime pairs with gap `n` occur
arbitrarily far out. -/
theorem polignacProperty_iff (n : ℕ) :
    PolignacProperty n ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsPrimeGap n p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    exact infinite_of_unbounded (fun N => by
      obtain ⟨p, hlt, hp⟩ := h N; exact ⟨p, hp, hlt⟩)

/-! ### Sanity checks on the definition -/

/-- `3` and `5` are consecutive primes with gap `2`. -/
lemma isPrimeGap_two_three : IsPrimeGap 2 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q h1 h2
  interval_cases q
  decide

/-- `7` and `11` are consecutive primes with gap `4`. -/
lemma isPrimeGap_four_seven : IsPrimeGap 4 7 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q h1 h2
  interval_cases q <;> decide

/-! ### The evenness hypothesis is necessary -/

/-- If `n` is odd, then `p = 2` is the only prime with `p + n` prime. -/
theorem eq_two_of_odd_gap {n p : ℕ} (hn : Odd n) (hp : Nat.Prime p)
    (hpn : Nat.Prime (p + n)) : p = 2 := by
  by_contra hne
  have hpodd : Odd p := hp.odd_of_ne_two hne
  have heven : Even (p + n) := hpodd.add_odd hn
  have h2 : p + n = 2 := (Nat.Prime.even_iff hpn).mp heven
  have hp2 : 2 ≤ p := hp.two_le
  have hn1 : 1 ≤ n := hn.pos
  omega

/-- De Polignac's property fails for every odd `n`. -/
theorem not_polignacProperty_of_odd {n : ℕ} (hn : Odd n) : ¬ PolignacProperty n := by
  intro h
  have hsub : {p : ℕ | IsPrimeGap n p} ⊆ {2} := by
    rintro p ⟨hp, hpn, -⟩
    exact eq_two_of_odd_gap hn hp hpn
  exact h ((Set.finite_singleton 2).subset hsub)

/-! ### The Chinese remainder construction -/

/-- The `k`-th modulus used in the construction for gap `n`: the prime `2` for `k = 0`, and
the `(n+k)`-th prime (which exceeds `n`) otherwise. -/
noncomputable def modulusPrime (n k : ℕ) : ℕ :=
  if k = 0 then 2 else Nat.nth Nat.Prime (n + k)

/-- The residue that `r` is required to have modulo `modulusPrime n k`. -/
noncomputable def targetResidue (n k : ℕ) : ℕ :=
  if k = 0 then 1 else modulusPrime n k - k

lemma modulusPrime_prime (n k : ℕ) : Nat.Prime (modulusPrime n k) := by
  unfold modulusPrime
  split
  · exact Nat.prime_two
  · exact Nat.prime_nth_prime _

lemma modulusPrime_zero (n : ℕ) : modulusPrime n 0 = 2 := by simp [modulusPrime]

lemma lt_modulusPrime (n k : ℕ) (hk : 0 < k) : n < modulusPrime n k := by
  have h : n + k ≤ Nat.nth Nat.Prime (n + k) :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime).le_apply
  have : modulusPrime n k = Nat.nth Nat.Prime (n + k) := by
    simp [modulusPrime, hk.ne']
  omega

lemma modulusPrime_injOn (n : ℕ) (hn : 2 ≤ n) {k l : ℕ} (hkl : k ≠ l) :
    modulusPrime n k ≠ modulusPrime n l := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · exact absurd rfl hkl
    · have := lt_modulusPrime n l hl
      rw [modulusPrime_zero]
      omega
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · have := lt_modulusPrime n k hk
      rw [modulusPrime_zero]
      omega
    · have hk' : modulusPrime n k = Nat.nth Nat.Prime (n + k) := by simp [modulusPrime, hk.ne']
      have hl' : modulusPrime n l = Nat.nth Nat.Prime (n + l) := by simp [modulusPrime, hl.ne']
      rw [hk', hl']
      intro h
      exact hkl (by
        have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h
        omega)

/-- Main construction: for even `n ≥ 2` there is an admissible pair of linear forms
`m ↦ r + M m`, `m ↦ r + n + M m` such that all intermediate values `r + M m + k`
(`0 < k < n`) have a nontrivial divisor bounded by `M`. -/
lemma exists_admissible (n : ℕ) (hn : 2 ≤ n) (hev : Even n) :
    ∃ r M : ℕ, 0 < M ∧
      (∀ q : ℕ, Nat.Prime q → ∃ m : ℕ, ¬ q ∣ (r + M * m) ∧ ¬ q ∣ (r + n + M * m)) ∧
      (∀ k : ℕ, 0 < k → k < n → ∃ d : ℕ, 1 < d ∧ d ≤ M ∧ d ∣ M ∧ d ∣ (r + k)) := by
  classical
  set s : ℕ → ℕ := modulusPrime n with hs_def
  set a : ℕ → ℕ := targetResidue n with ha_def
  have hsp : ∀ k, Nat.Prime (s k) := fun k => modulusPrime_prime n k
  have hs0 : s 0 = 2 := modulusPrime_zero n
  have hsk : ∀ k, 0 < k → n < s k := fun k hk => lt_modulusPrime n k hk
  have hnz : ∀ i ∈ Finset.range n, s i ≠ 0 := fun i _ => (hsp i).pos.ne'
  have hcop : (↑(Finset.range n) : Set ℕ).Pairwise (Function.onFun Nat.Coprime s) := by
    intro k _ l _ hkl
    exact (Nat.coprime_primes (hsp k) (hsp l)).mpr (modulusPrime_injOn n hn hkl)
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfFinset a s (Finset.range n) hnz hcop
  set M : ℕ := ∏ k ∈ Finset.range n, s k with hM_def
  have hMpos : 0 < M := Finset.prod_pos (fun i _ => (hsp i).pos)
  have hdvdM : ∀ k ∈ Finset.range n, s k ∣ M := fun k hk => Finset.dvd_prod_of_mem s hk
  have hsleM : ∀ k ∈ Finset.range n, s k ≤ M := fun k hk => Nat.le_of_dvd hMpos (hdvdM k hk)
  have h0mem : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h2M : 2 ∣ M := by rw [← hs0]; exact hdvdM 0 h0mem
  -- `r` is odd
  have hrodd : ¬ (2 ∣ r) := by
    have h := hr 0 h0mem
    rw [hs0] at h
    have ha0 : a 0 = 1 := by simp [ha_def, targetResidue]
    rw [ha0] at h
    have h1 : r % 2 = 1 % 2 := h
    intro hdvd
    omega
  -- divisibility of the intermediate values
  have hkey : ∀ k : ℕ, 0 < k → k < n → s k ∣ (r + k) := by
    intro k hk hkn
    have hmem : k ∈ Finset.range n := Finset.mem_range.mpr hkn
    have h := (hr k hmem).add_right k
    have hle : k ≤ s k := le_of_lt (lt_of_lt_of_le hkn (le_of_lt (hsk k hk)))
    have hak : a k = s k - k := by simp [ha_def, hs_def, targetResidue, hk.ne']
    rw [hak, Nat.sub_add_cancel hle] at h
    have h0 : (r + k) ≡ 0 [MOD s k] := h.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl)
    exact (Nat.modEq_zero_iff_dvd).mp h0
  refine ⟨r, M, hMpos, ?_, ?_⟩
  · -- admissibility
    intro q hq
    by_cases hqM : q ∣ M
    · obtain ⟨k, hk, hqk⟩ := (hq.prime).exists_mem_finset_dvd hqM
      have hqsk : q = s k := (Nat.prime_dvd_prime_iff_eq hq (hsp k)).mp hqk
      refine ⟨0, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [hqsk, hs0]
          simpa using hrodd
        · rw [hqsk]
          simp only [Nat.mul_zero, Nat.add_zero]
          intro hdvd
          have hdk : s k ∣ k := by
            have h := Nat.dvd_sub (hkey k hkpos (Finset.mem_range.mp hk)) hdvd
            simpa using h
          exact absurd (Nat.le_of_dvd hkpos hdk) (by
            have := hsk k hkpos
            have := Finset.mem_range.mp hk
            omega)
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · rw [hqsk, hs0]
          simp only [Nat.mul_zero, Nat.add_zero]
          obtain ⟨t, ht⟩ := hev
          intro hdvd
          exact hrodd (by omega)
        · rw [hqsk]
          simp only [Nat.mul_zero, Nat.add_zero]
          intro hdvd
          have hkn := Finset.mem_range.mp hk
          have hdk : s k ∣ (n - k) := by
            have h := Nat.dvd_sub hdvd (hkey k hkpos hkn)
            have he : r + n - (r + k) = n - k := by omega
            rwa [he] at h
          have := Nat.le_of_dvd (by omega) hdk
          have := hsk k hkpos
          omega
    · -- `q` does not divide `M`; in particular `q` is odd
      have hq2 : q ≠ 2 := by rintro rfl; exact hqM h2M
      haveI : Fact (Nat.Prime q) := ⟨hq⟩
      by_contra hcon
      push_neg at hcon
      have hbad : ∀ m : ℕ, q ∣ (r + M * m) ∨ q ∣ (r + n + M * m) := fun m =>
        or_iff_not_imp_left.mpr (hcon m)
      have key : ∀ m : ℕ,
          ((r : ZMod q) + (M : ZMod q) * (m : ZMod q) = 0) ∨
          ((r : ZMod q) + (n : ZMod q) + (M : ZMod q) * (m : ZMod q) = 0) := by
        intro m
        rcases hbad m with h | h
        · left
          have h' : ((r + M * m : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
          push_cast at h'
          linear_combination h'
        · right
          have h' : ((r + n + M * m : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
          push_cast at h'
          linear_combination h'
      have hu : (M : ZMod q) ≠ 0 := fun h => hqM ((ZMod.natCast_eq_zero_iff _ _).mp h)
      have h2ne : (2 : ZMod q) ≠ 0 := by
        have : ((2 : ℕ) : ZMod q) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd
          exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd)
        simpa using this
      have k0 := key 0
      have k1 := key 1
      have k2 := key 2
      push_cast at k0 k1 k2
      rcases k0 with h0 | h0 <;> rcases k1 with h1 | h1 <;> rcases k2 with h2 | h2 <;>
        first
          | exact hu (by linear_combination h1 - h0)
          | exact hu (by linear_combination h2 - h1)
          | (rcases mul_eq_zero.mp (show (2 : ZMod q) * (M : ZMod q) = 0 by
                linear_combination h2 - h0) with h | h
             · exact h2ne h
             · exact hu h)
  · -- intermediate values are composite
    intro k hk hkn
    have hmem : k ∈ Finset.range n := Finset.mem_range.mpr hkn
    exact ⟨s k, (hsp k).one_lt, hsleM k hmem, hdvdM k hmem, hkey k hk hkn⟩

/-! ### The conditional theorem -/

/-- **De Polignac's conjecture, conditional on a two-form case of Dickson's conjecture.** -/
theorem PolignacConjecture (hD : DicksonPairHypothesis) :
    ∀ n : ℕ, 0 < n → Even n → PolignacProperty n := by
  intro n hn hev
  have hn2 : 2 ≤ n := by obtain ⟨t, ht⟩ := hev; omega
  obtain ⟨r, M, hMpos, hadm, hcomp⟩ := exists_admissible n hn2 hev
  apply infinite_of_unbounded
  intro N
  obtain ⟨m, hmN, hp1, hp2⟩ := hD r M n hMpos hn hadm (max (N + 1) 2)
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hmN
  have hmN' : N + 1 ≤ m := le_trans (le_max_left _ _) hmN
  have hMm : M * 2 ≤ M * m := Nat.mul_le_mul_left M hm2
  have hmle : m ≤ M * m := Nat.le_mul_of_pos_left m hMpos
  have hp2' : Nat.Prime (r + M * m + n) := by
    have : r + M * m + n = r + n + M * m := by omega
    rw [this]; exact hp2
  refine ⟨r + M * m, ⟨hp1, hp2', ?_⟩, by omega⟩
  intro q hq1 hq2 hqp
  obtain ⟨k, hk⟩ : ∃ k, q = (r + M * m) + k := ⟨q - (r + M * m), by omega⟩
  obtain ⟨d, hd1, hdM, hdvdM, hdr⟩ := hcomp k (by omega) (by omega)
  have hdq : d ∣ q := by
    have : q = (r + k) + M * m := by omega
    rw [this]
    exact Nat.dvd_add hdr (Dvd.dvd.mul_right hdvdM m)
  have hdeq : d = q := (hqp.eq_one_or_self_of_dvd d hdq).resolve_left (by omega)
  omega

/-- Twin primes, as the special case `n = 2`. -/
theorem twin_primes_of_dickson (hD : DicksonPairHypothesis) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  have h := PolignacConjecture hD 2 (by norm_num) (by decide)
  refine h.mono ?_
  rintro p ⟨hp, hp2, -⟩
  exact ⟨hp, hp2⟩

end Brockian.PolignacPrimes

