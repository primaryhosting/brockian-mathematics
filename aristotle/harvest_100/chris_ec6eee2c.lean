import Mathlib
/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, the gap between the `n`-th and `(n+1)`-st prime
(with `p_0 = 2`, i.e. `p_n = Nat.nth Nat.Prime n`). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The "two primes in a bounded window" statement: there is a bound `B` such that
arbitrarily far out one finds two distinct primes `p < q` with `q ≤ p + B`. -/
def TwoPrimesInBoundedWindow : Prop :=
  ∃ B : ℕ, ∀ N : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N ≤ p ∧ p < q ∧ q ≤ p + B

/-- The Goldston–Pintz–Yıldırım / Zhang / Maynard statement `DHL[k, 2]`: there is a finite
set of shifts `H` (in the applications, an admissible `k`-tuple) such that for arbitrarily
large `n` at least two of the numbers `n + h`, `h ∈ H`, are prime. -/
def DHL2 : Prop :=
  ∃ H : Finset ℕ, ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ 2 ≤ (H.filter (fun h => Nat.Prime (n + h))).card

private lemma primes_infinite : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime

/-- If `p < q` are primes, then the prime immediately after `p` is at most `q`. -/
lemma nth_succ_count_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) ≤ q := by
  have h1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    rw [Nat.count_succ, if_pos hp]
  have h2 : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q := by
    rw [← h1]; exact Nat.count_monotone _ hpq
  calc Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1)
      ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) := (Nat.nth_le_nth primes_infinite).2 h2
    _ = q := Nat.nth_count hq

/-- `DHL[k,2]` implies that two primes occur in a window of bounded length, arbitrarily
far out. -/
theorem twoPrimesInBoundedWindow_of_DHL2 (h : DHL2) : TwoPrimesInBoundedWindow := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.sup id, fun N => ?_⟩
  obtain ⟨n, hn, hcard⟩ := hH N
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_filter] at ha hb
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨n + a, n + b, ha.2, hb.2, le_add_right hn, by omega,
      by have := Finset.le_sup (f := id) hb.1; simp at this; omega⟩
  · exact ⟨n + b, n + a, hb.2, ha.2, le_add_right hn, by omega,
      by have := Finset.le_sup (f := id) ha.1; simp at this; omega⟩

/-- From two primes in a bounded window, arbitrarily far out, we get a uniform bound on
infinitely many *consecutive* prime gaps. -/
theorem exists_bound_frequently_gap_le (h : TwoPrimesInBoundedWindow) :
    ∃ B : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ primeGap n ≤ B := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun N => ?_⟩
  obtain ⟨p, q, hp, hq, hNp, hpq, hqB⟩ := hB (Nat.nth Nat.Prime N + 1)
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · have hlt : Nat.nth Nat.Prime N < Nat.nth Nat.Prime (Nat.count Nat.Prime p) := by
      rw [Nat.nth_count hp]; omega
    exact ((Nat.nth_lt_nth primes_infinite).1 hlt).le
  · have := nth_succ_count_le hp hq hpq
    rw [primeGap, Nat.nth_count hp]
    omega

/-- The set of indices with gap at most `B` is frequently hit, phrased with `Filter`. -/
theorem frequently_gap_le (h : TwoPrimesInBoundedWindow) :
    ∃ B : ℕ, ∃ᶠ n in atTop, primeGap n ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_frequently_gap_le h
  refine ⟨B, ?_⟩
  rw [frequently_atTop]
  exact fun N => hB N

/-- **Bounded prime gaps** (Zhang / Maynard), stated as: the `liminf` of the sequence of
consecutive prime gaps is finite.

This is a Lean-checked *reduction*: the conclusion is derived from the
Goldston–Pintz–Yıldırım-type hypothesis `DHL2`, which is exactly what the sieve-theoretic
work of Zhang and Maynard establishes. -/
theorem bounded_prime_gaps (h : DHL2) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop ≠ ⊤ := by
  obtain ⟨B, hB⟩ := frequently_gap_le (twoPrimesInBoundedWindow_of_DHL2 h)
  have hle : liminf (fun n => (primeGap n : ℕ∞)) atTop ≤ (B : ℕ∞) :=
    liminf_le_of_frequently_le (hB.mono fun n hn => by exact_mod_cast hn)
  intro htop
  rw [htop] at hle
  simp at hle

/-- Conversely (and unconditionally), finiteness of the `liminf` of prime gaps is
equivalent to the "two primes in a bounded window" statement. -/
theorem twoPrimesInBoundedWindow_iff_liminf_ne_top :
    TwoPrimesInBoundedWindow ↔ liminf (fun n => (primeGap n : ℕ∞)) atTop ≠ ⊤ := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := frequently_gap_le h
    have hle : liminf (fun n => (primeGap n : ℕ∞)) atTop ≤ (B : ℕ∞) :=
      liminf_le_of_frequently_le (hB.mono fun n hn => by exact_mod_cast hn)
    intro htop
    rw [htop] at hle
    simp at hle
  · intro h
    obtain ⟨L, hL⟩ : ∃ L : ℕ, liminf (fun n => (primeGap n : ℕ∞)) atTop < (L : ℕ∞) := by
      obtain ⟨L, hLeq⟩ := ENat.ne_top_iff_exists.1 h
      refine ⟨L + 1, ?_⟩
      rw [← hLeq]
      exact_mod_cast Nat.lt_succ_self L
    have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) < (L : ℕ∞) :=
      frequently_lt_of_liminf_lt (h := hL)
    refine ⟨L, fun N => ?_⟩
    rw [frequently_atTop] at hfreq
    obtain ⟨n, hn, hgap⟩ := hfreq N
    have hgap' : primeGap n < L := by exact_mod_cast hgap
    refine ⟨Nat.nth Nat.Prime n, Nat.nth Nat.Prime (n + 1), Nat.prime_nth_prime n,
      Nat.prime_nth_prime (n + 1), ?_, ?_, ?_⟩
    · exact le_trans hn (Nat.le_nth fun hf => absurd hf primes_infinite)
    · exact (Nat.nth_lt_nth primes_infinite).2 (Nat.lt_succ_self n)
    · have hmono : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1) :=
        ((Nat.nth_lt_nth primes_infinite).2 (Nat.lt_succ_self n)).le
      have : primeGap n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n := rfl
      omega

/-! ### Base cases and a further reduction -/

lemma nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rwa [hc] at h

lemma nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  rwa [hc] at h

lemma nth_prime_two : Nat.nth Nat.Prime 2 = 5 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 5) (by norm_num)
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  rwa [hc] at h

/-- Base case: the first prime gap is `3 - 2 = 1`. -/
lemma primeGap_zero : primeGap 0 = 1 := by
  rw [primeGap, nth_prime_zero, nth_prime_one]

/-- The second prime gap is `5 - 3 = 2`. -/
lemma primeGap_one : primeGap 1 = 2 := by
  rw [primeGap, nth_prime_one, nth_prime_two]

/-- The twin prime conjecture, in the form: there are arbitrarily large primes `p` with
`p + 2` prime. -/
def TwinPrimeConjecture : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ (p + 2).Prime

/-- The twin prime conjecture implies `DHL[k,2]` (with the admissible pair `{0, 2}`), and
hence bounded prime gaps. -/
theorem dhl2_of_twinPrimeConjecture (h : TwinPrimeConjecture) : DHL2 := by
  refine ⟨{0, 2}, fun N => ?_⟩
  obtain ⟨p, hNp, hp, hp2⟩ := h N
  refine ⟨p, hNp, ?_⟩
  have hfil : ({0, 2} : Finset ℕ).filter (fun k => Nat.Prime (p + k)) = {0, 2} := by
    refine Finset.filter_true_of_mem fun k hk => ?_
    fin_cases hk
    · simpa using hp
    · simpa using hp2
  rw [hfil]
  decide

/-- Consequence: the twin prime conjecture implies that the `liminf` of prime gaps is
finite. -/
theorem bounded_prime_gaps_of_twinPrimeConjecture (h : TwinPrimeConjecture) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop ≠ ⊤ :=
  bounded_prime_gaps (dhl2_of_twinPrimeConjecture h)

end Frontier

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

