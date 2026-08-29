/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter

namespace Frontier

/-- The `n`-th prime number (`primeSeq 0 = 2`). -/
noncomputable def primeSeq (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap `p_{n+1} - p_n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := primeSeq (n + 1) - primeSeq n

/-- The set of primes is infinite. -/
theorem setOf_prime_infinite : {p : ℕ | p.Prime}.Infinite :=
  Nat.infinite_setOf_prime

/-- **Bounded prime gaps** (the "small gaps between primes" statement): some bound `B`
is attained by infinitely many prime gaps. -/
def BoundedPrimeGaps : Prop := ∃ B : ℕ, {n : ℕ | primeGap n ≤ B}.Infinite

/-- The hypothesis supplied by the Zhang–Maynard–Tao theorem: there is a positive shift `d`
such that `p` and `p + d` are simultaneously prime for infinitely many `p`. -/
def InfinitelyManyPrimePairs : Prop :=
  ∃ d : ℕ, 0 < d ∧ {p : ℕ | p.Prime ∧ (p + d).Prime}.Infinite

section Reduction

/-- If `q` is a prime larger than the `n`-th prime, then the `(n+1)`-st prime is at most `q`. -/
theorem primeSeq_succ_le_of_prime {n q : ℕ} (hq : q.Prime) (h : primeSeq n < q) :
    primeSeq (n + 1) ≤ q := by
  by_contra hcon
  push_neg at hcon
  exact absurd (Nat.le_nth_of_lt_nth_succ hcon hq) (not_le.mpr h)

/-- Every prime is the `n`-th prime for `n = π(q) - 1`, i.e. `n = Nat.count Nat.Prime q`. -/
theorem primeSeq_count {q : ℕ} (hq : q.Prime) : primeSeq (Nat.count Nat.Prime q) = q :=
  Nat.nth_count hq

/-- If `p` and `p + d` are both prime, then the prime gap at index `Nat.count Nat.Prime p`
is at most `d`. -/
theorem primeGap_le_of_prime_pair {p d : ℕ} (hp : p.Prime) (hpd : (p + d).Prime) (hd : 0 < d) :
    primeGap (Nat.count Nat.Prime p) ≤ d := by
  have h1 : primeSeq (Nat.count Nat.Prime p) = p := primeSeq_count hp
  have h2 : primeSeq (Nat.count Nat.Prime p + 1) ≤ p + d := by
    refine primeSeq_succ_le_of_prime hpd ?_
    rw [h1]; omega
  unfold primeGap
  omega

/-- A prime pair with shift `d` above any given bound produces a prime-gap index above any
given bound. -/
theorem exists_gap_index_gt (d : ℕ) (hd : 0 < d)
    (hinf : {p : ℕ | p.Prime ∧ (p + d).Prime}.Infinite) (N : ℕ) :
    ∃ n, N < n ∧ primeGap n ≤ d := by
  obtain ⟨p, hp, hpN⟩ := hinf.exists_gt (primeSeq N)
  refine ⟨Nat.count Nat.Prime p, ?_, primeGap_le_of_prime_pair hp.1 hp.2 hd⟩
  have hcount : primeSeq (Nat.count Nat.Prime p) = p := primeSeq_count hp.1
  have : primeSeq N < primeSeq (Nat.count Nat.Prime p) := by rw [hcount]; exact hpN
  exact (Nat.nth_lt_nth setOf_prime_infinite).1 this

/-- **Reduction**: infinitely many prime pairs with a common shift imply bounded prime gaps. -/
theorem boundedPrimeGaps_of_infinitelyManyPrimePairs (H : InfinitelyManyPrimePairs) :
    BoundedPrimeGaps := by
  obtain ⟨d, hd, hinf⟩ := H
  refine ⟨d, Set.infinite_of_not_bddAbove ?_⟩
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hgap⟩ := exists_gap_index_gt d hd hinf N
  exact absurd (hN hgap) (not_le.mpr hn)

end Reduction

/-- Bounded prime gaps, expressed as finiteness of `liminf (p_{n+1} - p_n)` in `ℕ∞`. -/
theorem liminf_primeGap_lt_top_of_boundedPrimeGaps (H : BoundedPrimeGaps) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  obtain ⟨B, hB⟩ := H
  have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) ≤ (B : ℕ∞) := by
    have : ∃ᶠ n in atTop, primeGap n ≤ B := Nat.frequently_atTop_iff_infinite.2 hB
    exact this.mono fun n hn => by exact_mod_cast hn
  refine lt_of_le_of_lt (Filter.liminf_le_of_frequently_le' hfreq) ?_
  exact WithTop.coe_lt_top (B : ℕ)

/-- Conversely, finiteness of the `liminf` of the prime gaps gives a bound attained
infinitely often, so the two formulations of bounded prime gaps agree. -/
theorem boundedPrimeGaps_of_liminf_primeGap_lt_top
    (H : liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤) : BoundedPrimeGaps := by
  set L := liminf (fun n => (primeGap n : ℕ∞)) atTop with hL
  obtain ⟨B, hB⟩ : ∃ B : ℕ, L = (B : ℕ∞) := ⟨L.toNat, by
    lift L to ℕ using H.ne_top with m
    simp⟩
  refine ⟨B, ?_⟩
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hev : ∀ᶠ n in atTop, ((B + 1 : ℕ) : ℕ∞) ≤ (primeGap n : ℕ∞) := by
    have hnf : ¬ ∃ᶠ n in atTop, primeGap n ≤ B := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact Set.not_infinite.2 hfin
    rw [Filter.not_frequently] at hnf
    filter_upwards [hnf] with n hn
    have : B + 1 ≤ primeGap n := by omega
    exact_mod_cast this
  have h2 := Filter.le_liminf_of_le (by isBoundedDefault) hev
  rw [← hL, hB] at h2
  have : (B + 1 : ℕ) ≤ (B : ℕ) := by exact_mod_cast h2
  omega

/-- The two formulations of bounded prime gaps are equivalent. -/
theorem boundedPrimeGaps_iff_liminf_lt_top :
    BoundedPrimeGaps ↔ liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ :=
  ⟨liminf_primeGap_lt_top_of_boundedPrimeGaps, boundedPrimeGaps_of_liminf_primeGap_lt_top⟩

section BaseCases

/-- A prime `q` is the `n`-th prime as soon as exactly `n` primes are smaller than `q`. -/
theorem primeSeq_eq_of_count {n q : ℕ} (hq : q.Prime) (h : Nat.count Nat.Prime q = n) :
    primeSeq n = q := by
  subst h; exact Nat.nth_count hq

theorem primeSeq_zero : primeSeq 0 = 2 := primeSeq_eq_of_count (by norm_num) (by decide)
theorem primeSeq_one : primeSeq 1 = 3 := primeSeq_eq_of_count (by norm_num) (by decide)
theorem primeSeq_two : primeSeq 2 = 5 := primeSeq_eq_of_count (by norm_num) (by decide)
theorem primeSeq_three : primeSeq 3 = 7 := primeSeq_eq_of_count (by norm_num) (by decide)
theorem primeSeq_four : primeSeq 4 = 11 := primeSeq_eq_of_count (by norm_num) (by decide)
theorem primeSeq_five : primeSeq 5 = 13 := primeSeq_eq_of_count (by norm_num) (by decide)

theorem primeGap_zero : primeGap 0 = 1 := by
  simp [primeGap, primeSeq_zero, primeSeq_one]

theorem primeGap_one : primeGap 1 = 2 := by
  simp [primeGap, primeSeq_one, primeSeq_two]

theorem primeGap_two : primeGap 2 = 2 := by
  simp [primeGap, primeSeq_two, primeSeq_three]

theorem primeGap_three : primeGap 3 = 4 := by
  simp [primeGap, primeSeq_three, primeSeq_four]

theorem primeGap_four : primeGap 4 = 2 := by
  simp [primeGap, primeSeq_four, primeSeq_five]

end BaseCases

/-- **Bounded prime gaps** (Zhang, Maynard–Tao), as a Lean-checked reduction.

Granted the arithmetic input `H` — that for some positive shift `d` there are infinitely many
primes `p` with `p + d` also prime (this is exactly what the Zhang / Maynard–Tao theorem
provides) — the sequence of prime gaps `p_{n+1} - p_n` has finite `liminf`, and indeed some
bound is attained by infinitely many gaps. -/
theorem bounded_prime_gaps (H : InfinitelyManyPrimePairs) :
    (∃ B : ℕ, {n : ℕ | primeSeq (n + 1) - primeSeq n ≤ B}.Infinite) ∧
      liminf (fun n => ((primeSeq (n + 1) - primeSeq n : ℕ) : ℕ∞)) atTop < ⊤ := by
  have h := boundedPrimeGaps_of_infinitelyManyPrimePairs H
  exact ⟨h, liminf_primeGap_lt_top_of_boundedPrimeGaps h⟩

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

