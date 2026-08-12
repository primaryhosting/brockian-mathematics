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
-/

import Mathlib

/-!
Polignac's conjecture (1849) asserts that for every positive even number `n` there are
infinitely many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is open
(the case `n = 2` is the twin prime conjecture).

This file gives a Lean-checked *conditional reduction*: Polignac's conjecture follows from
Dickson's conjecture for two linear forms `M x + a`, `M x + b` (the standard hypothesis that an
admissible system of linear forms simultaneously represents primes infinitely often).

The reduction is the classical sieve/congruence argument: given an even `n`, one produces an
arithmetic progression `M x + a` such that *all* of the intermediate values
`M x + a + 1, …, M x + a + (n-1)` are automatically composite, while the two forms
`M x + a` and `M x + a + n` are admissible.
-/

namespace Brockian.PolignacPrimes

/-- `q` is the prime immediately following `p`: both are prime, `p < q`, and nothing strictly
between them is prime. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ r, p < r → r < q → ¬ Nat.Prime r

/-- **Polignac's conjecture**: for every positive even `n` there are arbitrarily large primes `p`
such that `p` and `p + n` are consecutive primes. -/
def PolignacStatement : Prop :=
  ∀ n : ℕ, Even n → 0 < n → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ ConsecutivePrimes p (p + n)

/-- **Dickson's conjecture**, for the special case of two linear forms with a common leading
coefficient: if the pair of forms `M x + a`, `M x + b` is admissible (no prime divides
`(M x + a)(M x + b)` for all `x`), then both forms are simultaneously prime for arbitrarily
large `x`. -/
def DicksonHypothesis : Prop :=
  ∀ M a b : ℕ, 0 < M →
    (∀ p : ℕ, p.Prime → ∃ x : ℕ, ¬ p ∣ (M * x + a) ∧ ¬ p ∣ (M * x + b)) →
    ∀ N : ℕ, ∃ x : ℕ, N < x ∧ Nat.Prime (M * x + a) ∧ Nat.Prime (M * x + b)

/-- If `p` is a prime not dividing `u`, and `c`, `d` have the same parity, then some value of the
progression `u * x` avoids both residues `-c` and `-d` modulo `p`. -/
theorem exists_not_dvd_pair {p u c d : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u)
    (hpar : c % 2 = d % 2) :
    ∃ x : ℕ, ¬ p ∣ (u * x + c) ∧ ¬ p ∣ (u * x + d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu' : (u : ZMod p) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hu
  set S : Finset (ZMod p) := {0, (c : ZMod p) - (d : ZMod p)} with hS
  have hcard : S.card < Fintype.card (ZMod p) := by
    rw [ZMod.card p]
    rcases eq_or_lt_of_le hp.two_le with h2 | h2
    · -- `p = 2`, and by the parity assumption the two bad residues coincide
      have hp2 : p = 2 := h2.symm
      subst hp2
      have : (c : ZMod 2) = (d : ZMod 2) := by
        rw [← ZMod.natCast_mod c 2, ← ZMod.natCast_mod d 2, hpar]
      simp [hS, this]
    · exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by simpa using h2)
  obtain ⟨w, hw⟩ : ∃ w : ZMod p, w ∉ S := by
    by_contra hc
    push_neg at hc
    have : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    simp [this] at hcard
  have hw0 : w ≠ 0 := by
    intro h; exact hw (by simp [hS, h])
  have hwcd : w ≠ (c : ZMod p) - (d : ZMod p) := by
    intro h; exact hw (by simp [hS, h])
  refine ⟨((w - (c : ZMod p)) * (u : ZMod p)⁻¹).val, ?_, ?_⟩
  · intro hdvd
    have : ((u * ((w - (c : ZMod p)) * (u : ZMod p)⁻¹).val + c : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id] at this
    field_simp at this
    exact hw0 (by linear_combination this)
  · intro hdvd
    have : ((u * ((w - (c : ZMod p)) * (u : ZMod p)⁻¹).val + d : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id] at this
    field_simp at this
    apply hwcd
    linear_combination this

/-- For even `n` and any bound `N`, there is a positive `m` such that no prime `p ≤ N` divides
either `m` or `m + n`.  (A Chinese-remainder style avoidance argument.) -/
theorem exists_coprime_pair (n : ℕ) (hn : Even n) (N : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ p : ℕ, p.Prime → p ≤ N → ¬ p ∣ m ∧ ¬ p ∣ (m + n) := by
  have hpar : ∀ m : ℕ, m % 2 = (m + n) % 2 := by
    obtain ⟨k, hk⟩ := hn
    intro m; omega
  induction N with
  | zero =>
      exact ⟨1, one_pos, fun p hp hple => absurd hple (by have := hp.two_le; omega)⟩
  | succ N ih =>
      obtain ⟨m, hm0, hm⟩ := ih
      by_cases hq : (N + 1).Prime
      · by_cases hd : ¬ (N + 1) ∣ m ∧ ¬ (N + 1) ∣ (m + n)
        · refine ⟨m, hm0, fun p hp hple => ?_⟩
          rcases Nat.lt_or_ge p (N + 1) with h | h
          · exact hm p hp (by omega)
          · have hpe : p = N + 1 := by omega
            subst hpe; exact hd
        · have hfac : ¬ (N + 1) ∣ Nat.factorial N := by
            rw [hq.dvd_factorial]; omega
          obtain ⟨t, h1, h2⟩ :=
            exists_not_dvd_pair (p := N + 1) (u := Nat.factorial N) (c := m) (d := m + n)
              hq hfac (hpar m)
          refine ⟨Nat.factorial N * t + m, by omega, fun p hp hple => ?_⟩
          rcases Nat.lt_or_ge p (N + 1) with h | h
          · have hpf : p ∣ Nat.factorial N * t :=
              Dvd.dvd.mul_right (Nat.dvd_factorial hp.pos (by omega)) t
            refine ⟨fun hc => (hm p hp (by omega)).1 ((Nat.dvd_add_right hpf).1 hc), fun hc => ?_⟩
            refine (hm p hp (by omega)).2 ((Nat.dvd_add_right hpf).1 ?_)
            rwa [add_assoc] at hc
          · have hpe : p = N + 1 := by omega
            subst hpe
            exact ⟨h1, by rw [add_assoc]; exact h2⟩
      · refine ⟨m, hm0, fun p hp hple => hm p hp ?_⟩
        by_cases hpe : p = N + 1
        · exact absurd (hpe ▸ hp) hq
        · omega

/-- **Main result.**  Dickson's conjecture (for two linear forms) implies Polignac's conjecture. -/
theorem PolignacConjecture (H : DicksonHypothesis) : PolignacStatement := by
  intro n hn hn0 N
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn; omega
  obtain ⟨m, hm0, hm⟩ := exists_coprime_pair n hn n
  set J : Finset ℕ := (Finset.Ico 2 n).filter (fun j => Even j) with hJ
  set P : ℕ := ∏ j ∈ J, (m + j) with hP
  have hP0 : 0 < P := Finset.prod_pos (fun j _ => by omega)
  set M : ℕ := 2 * P with hM
  set a : ℕ := m + 2 * P with ha
  have hM0 : 0 < M := by omega
  have hmodd : ¬ 2 ∣ m := (hm 2 Nat.prime_two (by omega)).1
  have haodd : a % 2 = 1 := by omega
  have hpar : a % 2 = (a + n) % 2 := by obtain ⟨k, hk⟩ := hn; omega
  -- membership facts about `J`
  have hJmem : ∀ j ∈ J, 2 ≤ j ∧ j < n ∧ Even j := by
    intro j hj
    rw [hJ, Finset.mem_filter, Finset.mem_Ico] at hj
    exact ⟨hj.1.1, hj.1.2, hj.2⟩
  have hJdvd : ∀ j ∈ J, (m + j) ∣ P := fun j hj => Finset.dvd_prod_of_mem _ hj
  -- the prime divisors of `M` divide neither `a` nor `a + n`
  have hkey : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ a ∧ ¬ p ∣ (a + n) := by
    intro p hp hpM
    rcases (Nat.Prime.dvd_mul hp).1 hpM with h2 | hpP
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      subst hp2
      constructor
      · omega
      · obtain ⟨k, hk⟩ := hn; omega
    · obtain ⟨j, hjJ, hpj⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hpP
      obtain ⟨hj2, hjn, hje⟩ := hJmem j hjJ
      have hp2P : p ∣ 2 * P := Dvd.dvd.mul_left hpP 2
      constructor
      · intro hpa
        have hpm : p ∣ m := (Nat.dvd_add_iff_left hp2P).2 (by rw [ha] at hpa; exact hpa)
        have hpj' : p ∣ j := (Nat.dvd_add_right hpm).1 hpj
        have hple : p ≤ j := Nat.le_of_dvd (by omega) hpj'
        exact (hm p hp (by omega)).1 hpm
      · intro hpan
        have hpmn : p ∣ m + n := by
          refine (Nat.dvd_add_iff_left hp2P).2 ?_
          have : m + n + 2 * P = a + n := by rw [ha]; ring
          rw [this]; exact hpan
        have hsub : p ∣ n - j := by
          have := Nat.dvd_sub hpmn hpj
          have he : m + n - (m + j) = n - j := by omega
          rwa [he] at this
        have hple : p ≤ n - j := Nat.le_of_dvd (by omega) hsub
        exact (hm p hp (by omega)).2 hpmn
  -- admissibility of the pair of forms
  have hadm : ∀ p : ℕ, p.Prime → ∃ x : ℕ, ¬ p ∣ (M * x + a) ∧ ¬ p ∣ (M * x + (a + n)) := by
    intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨h1, h2⟩ := hkey p hp hpM
      exact ⟨0, by simpa using h1, by simpa using h2⟩
    · exact exists_not_dvd_pair hp hpM hpar
  obtain ⟨x, hxN, hpr1, hpr2⟩ := H M a (a + n) hM0 hadm N
  refine ⟨M * x + a, ?_, hpr1, ?_, ?_, ?_⟩
  · have : x ≤ M * x := Nat.le_mul_of_pos_left x hM0
    omega
  · have he : M * x + a + n = M * x + (a + n) := by ring
    rw [he]; exact hpr2
  · omega
  · intro r hr1 hr2 hrp
    set j : ℕ := r - (M * x + a) with hj
    have hrj : r = M * x + a + j := by omega
    have hj1 : 1 ≤ j := by omega
    have hjn : j < n := by omega
    rcases Nat.even_or_odd j with hje | hjo
    · -- even `j`: `m + j` is a nontrivial divisor of `r`
      have hj2 : 2 ≤ j := by
        rcases hje with ⟨k, hk⟩; omega
      have hjJ : j ∈ J := by
        rw [hJ, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨hj2, hjn⟩, hje⟩
      have hdvdP : (m + j) ∣ P := hJdvd j hjJ
      have hdvdr : (m + j) ∣ r := by
        have hr' : r = (m + j) + (2 * P * x + 2 * P) := by rw [hrj, ha, hM]; ring
        rw [hr']
        exact Dvd.dvd.add (dvd_refl _) (Dvd.dvd.add (Dvd.dvd.mul_right (hdvdP.mul_left 2) x)
          (hdvdP.mul_left 2))
      rcases (Nat.Prime.eq_one_or_self_of_dvd hrp (m + j) hdvdr) with h | h
      · omega
      · have : r = M * x + a + j := hrj
        rw [ha] at this
        omega
    · -- odd `j`: `r` is even and bigger than `2`
      have hdvd2 : 2 ∣ r := by
        rcases hjo with ⟨k, hk⟩
        have : M * x = 2 * (P * x) := by rw [hM]; ring
        omega
      rcases (Nat.Prime.eq_one_or_self_of_dvd hrp 2 hdvd2) with h | h
      · omega
      · omega

/-- Specialisation to `n = 2`: Dickson's conjecture implies the twin prime conjecture, in the
strong form that arbitrarily large twin primes are consecutive primes. -/
theorem twinPrimes_of_dickson (H : DicksonHypothesis) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ ConsecutivePrimes p (p + 2) :=
  PolignacConjecture H 2 (by decide) (by norm_num) N

end Brockian.PolignacPrimes

