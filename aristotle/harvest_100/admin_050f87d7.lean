/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean 4
does not allow a module docstring to precede the `import` commands.)
-/

open Filter

namespace Frontier

/-- The `n`-th prime number (`nthPrime 0 = 2`). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap, `p_{n+1} - p_n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

lemma primeSet_infinite : {p | Nat.Prime p}.Infinite := Nat.infinite_setOf_prime

lemma nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite primeSet_infinite n

lemma nthPrime_lt_nthPrime_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  (Nat.nth_lt_nth primeSet_infinite).2 (Nat.lt_succ_self n)

lemma nthPrime_strictMono : StrictMono nthPrime :=
  fun _ _ h => (Nat.nth_lt_nth primeSet_infinite).2 h

/-- The gap bound as an inequality between the primes themselves. -/
lemma nthPrime_succ_le_of_gap_le {n B : ℕ} (h : primeGap n ≤ B) :
    nthPrime (n + 1) ≤ nthPrime n + B := by
  have := nthPrime_lt_nthPrime_succ n
  unfold primeGap at h
  omega

/-- If `p` is prime and `q` is a larger prime, then the prime following `p` is at most `q`. -/
lemma nthPrime_succ_count_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    nthPrime (Nat.count Nat.Prime p + 1) ≤ q := by
  have hcount : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q := by
    have h1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 :=
      Nat.count_succ_eq_succ_count_iff.2 hp
    have h2 : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime q :=
      Nat.count_monotone _ hpq
    omega
  calc nthPrime (Nat.count Nat.Prime p + 1)
      ≤ nthPrime (Nat.count Nat.Prime q) :=
        (Nat.nth_le_nth primeSet_infinite).2 hcount
    _ = q := Nat.nth_count hq

lemma nthPrime_count {p : ℕ} (hp : p.Prime) : nthPrime (Nat.count Nat.Prime p) = p :=
  Nat.nth_count hp

/-- Frequently-small gaps are equivalent to the existence of arbitrarily large prime pairs
at bounded distance. -/
lemma frequently_gap_le_iff (B : ℕ) :
    (∃ᶠ n in atTop, primeGap n ≤ B) ↔
      ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B := by
  constructor
  · intro h N
    have htend : Tendsto nthPrime atTop atTop := nthPrime_strictMono.tendsto_atTop
    have hev : ∀ᶠ n in atTop, N ≤ nthPrime n := htend.eventually_ge_atTop N
    obtain ⟨n, hgap, hge⟩ := (h.and_eventually hev).exists
    exact ⟨nthPrime n, nthPrime (n + 1), hge, nthPrime_prime n, nthPrime_prime (n + 1),
      nthPrime_lt_nthPrime_succ n, nthPrime_succ_le_of_gap_le hgap⟩
  · intro h
    rw [frequently_atTop]
    intro M
    obtain ⟨p, q, hNp, hp, hq, hpq, hqp⟩ := h (nthPrime M + 1)
    refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
    · have : nthPrime M < nthPrime (Nat.count Nat.Prime p) := by
        rw [nthPrime_count hp]; omega
      exact le_of_lt (nthPrime_strictMono.lt_iff_lt.1 this)
    · have h1 : nthPrime (Nat.count Nat.Prime p + 1) ≤ q := nthPrime_succ_count_le hp hq hpq
      have h2 : nthPrime (Nat.count Nat.Prime p) = p := nthPrime_count hp
      unfold primeGap
      omega

/-- `liminf` over `ℕ∞` is finite iff the sequence is frequently bounded by some natural number. -/
lemma liminf_lt_top_iff (f : ℕ → ℕ) :
    liminf (fun n => (f n : ℕ∞)) atTop < ⊤ ↔ ∃ B : ℕ, ∃ᶠ n in atTop, f n ≤ B := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.1 h.ne
    refine ⟨L, ?_⟩
    by_contra hcon
    rw [not_frequently] at hcon
    have hev : ∀ᶠ n in atTop, ((L : ℕ∞) + 1) ≤ (f n : ℕ∞) := by
      filter_upwards [hcon] with n hn
      have : L + 1 ≤ f n := by omega
      exact_mod_cast this
    have : ((L : ℕ∞) + 1) ≤ liminf (fun n => (f n : ℕ∞)) atTop := by
      rw [liminf_eq]
      exact le_sSup hev
    rw [← hL] at this
    have hfin : L + 1 ≤ L := by exact_mod_cast this
    omega
  · rintro ⟨B, hB⟩
    refine lt_of_le_of_lt (liminf_le_of_frequently_le' (x := (B : ℕ∞)) ?_) ?_
    · exact hB.mono fun n hn => by exact_mod_cast hn
    · exact WithTop.coe_lt_top B

/--
**Bounded prime gaps** (Zhang–Maynard), stated as a Lean-checked reduction.

The assertion that the liminf of the prime gaps `p_{n+1} - p_n` is finite is *equivalent*
to the assertion proved by Zhang and Maynard: there is a bound `B` such that arbitrarily
large pairs of primes `p < q` satisfy `q ≤ p + B`.
-/
theorem bounded_prime_gaps :
    liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ ↔
      ∃ B : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B := by
  rw [liminf_lt_top_iff]
  exact exists_congr fun B => frequently_gap_le_iff B

/--
Quantitative form of the reduction: if arbitrarily large pairs of primes `p < q` with
`q ≤ p + B` exist, then the liminf of the prime gaps is at most `B`.
-/
theorem liminf_primeGap_le_of_bounded_prime_pairs (B : ℕ)
    (h : ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop ≤ (B : ℕ∞) :=
  liminf_le_of_frequently_le'
    (((frequently_gap_le_iff B).2 h).mono fun n hn => by exact_mod_cast hn)

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

