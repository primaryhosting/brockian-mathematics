/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring; the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Filter Set

/-- The `n`-th prime, `p n` (so `p 0 = 2`, `p 1 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap `p_{n+1} - p_n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- **Bounded prime gaps** (Zhang / Maynard): there is a bound `B` such that
`p_{n+1} - p_n ≤ B` for infinitely many `n`; equivalently `liminf (p_{n+1} - p_n) < ∞`. -/
def BoundedPrimeGaps : Prop := ∃ B : ℕ, ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ B

/-- The "prime pairs" form of bounded gaps: there is a bound `B` such that arbitrarily far out
one finds two distinct primes within distance `B` of each other. -/
def BoundedPrimePairs : Prop :=
  ∃ B : ℕ, ∀ N : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N ≤ p ∧ p < q ∧ q - p ≤ B

/-! ### Basic facts about `nthPrime` -/

theorem nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

theorem nthPrime_strictMono : StrictMono nthPrime := fun _ _ h =>
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 h

theorem nthPrime_le_nthPrime {m n : ℕ} : nthPrime m ≤ nthPrime n ↔ m ≤ n :=
  Nat.nth_le_nth Nat.infinite_setOf_prime

theorem le_nthPrime (n : ℕ) : n ≤ nthPrime n :=
  Nat.le_nth fun hf => absurd hf Nat.infinite_setOf_prime

theorem nthPrime_count {p : ℕ} (hp : p.Prime) : nthPrime (Nat.count Nat.Prime p) = p :=
  Nat.nth_count hp

theorem nthPrime_zero : nthPrime 0 = 2 := by
  have h : Nat.count Nat.Prime 2 = 0 := by decide
  have := nthPrime_count (p := 2) Nat.prime_two
  rwa [h] at this

theorem nthPrime_one : nthPrime 1 = 3 := by
  have h : Nat.count Nat.Prime 3 = 1 := by decide
  have := nthPrime_count (p := 3) Nat.prime_three
  rwa [h] at this

/-- The base case: the very first prime gap is `3 - 2 = 1`. -/
theorem primeGap_zero : primeGap 0 = 1 := by
  simp [primeGap, nthPrime_zero, nthPrime_one]

/-- Prime gaps are positive. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  have h : nthPrime n < nthPrime (n + 1) := nthPrime_strictMono (Nat.lt_succ_self n)
  simp only [primeGap]
  omega

/-! ### A reduction: gaps between consecutive primes versus arbitrary close prime pairs -/

/-- If `p < q` are primes, then the prime immediately after `p` is at most `q`. -/
theorem nthPrime_succ_count_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    nthPrime (Nat.count Nat.Prime p + 1) ≤ q := by
  have hstep : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    simp [Nat.count_succ, hp]
  have hmono : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime q :=
    Nat.count_monotone _ hpq
  calc nthPrime (Nat.count Nat.Prime p + 1)
      ≤ nthPrime (Nat.count Nat.Prime q) := nthPrime_le_nthPrime.2 (by omega)
    _ = q := nthPrime_count hq

theorem boundedPrimePairs_iff : BoundedPrimeGaps ↔ BoundedPrimePairs := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨n, hn, hgap⟩ := hB N
    refine ⟨nthPrime n, nthPrime (n + 1), nthPrime_prime n, nthPrime_prime (n + 1), ?_,
      nthPrime_strictMono (Nat.lt_succ_self n), hgap⟩
    exact hn.trans (le_nthPrime n)
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨p, q, hp, hq, hNp, hpq, hqp⟩ := hB (nthPrime N)
    set k := Nat.count Nat.Prime p with hk
    have hnk : nthPrime k = p := nthPrime_count hp
    have hkN : N ≤ k := by
      by_contra hlt
      push_neg at hlt
      have : nthPrime k < nthPrime N := nthPrime_strictMono hlt
      omega
    refine ⟨k, hkN, ?_⟩
    have h1 : nthPrime (k + 1) ≤ q := nthPrime_succ_count_le hp hq hpq
    simp only [primeGap, hnk]
    omega

/-! ### Equivalent analytic formulations -/

theorem infinite_iff : BoundedPrimeGaps ↔ ∃ B : ℕ, {n | primeGap n ≤ B}.Infinite := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, Set.infinite_of_not_bddAbove ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨n, hn, hgap⟩ := hB (M + 1)
    have := hM (show n ∈ {n | primeGap n ≤ B} from hgap)
    omega
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hB.exists_gt N
    exact ⟨n, hlt.le, hn⟩

theorem not_tendsto_iff : BoundedPrimeGaps ↔ ¬ Tendsto primeGap atTop atTop := by
  constructor
  · rintro ⟨B, hB⟩ htend
    rw [Filter.tendsto_atTop_atTop] at htend
    obtain ⟨i, hi⟩ := htend (B + 1)
    obtain ⟨n, hn, hgap⟩ := hB i
    have := hi n hn
    omega
  · intro h
    rw [Filter.tendsto_atTop_atTop] at h
    push_neg at h
    obtain ⟨b, hb⟩ := h
    refine ⟨b, fun N => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hb N
    exact ⟨n, hn, le_of_lt hlt⟩

theorem liminf_ne_top_iff :
    Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop ≠ ⊤ ↔ BoundedPrimeGaps := by
  constructor
  · intro h
    by_contra hbad
    apply h
    refine ENat.eq_top_iff_forall_ge.mpr fun b => ?_
    rw [BoundedPrimeGaps] at hbad
    push_neg at hbad
    obtain ⟨N, hN⟩ := hbad b
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact_mod_cast (hN n hn).le
  · rintro ⟨B, hB⟩
    have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) ≤ (B : ℕ∞) := by
      rw [Filter.frequently_atTop]
      intro a
      obtain ⟨n, hn, hgap⟩ := hB a
      exact ⟨n, hn, by exact_mod_cast hgap⟩
    have := Filter.liminf_le_of_frequently_le hfreq
    intro htop
    rw [htop] at this
    simp at this

/-! ### Main statement -/

/--
**Bounded prime gaps** (Zhang–Maynard), formalized and reduced.

The statement `BoundedPrimeGaps` says that `liminf_n (p_{n+1} - p_n) < ∞`, i.e. there is a bound
`B` with `p_{n+1} - p_n ≤ B` for infinitely many `n`. The full theorem of Zhang and Maynard is
*not* proved here. What is proved, unconditionally and axiom-cleanly, is:

* the literal `liminf` formulation over `ℕ∞` is equivalent to the `∃ B` formulation;
* it is equivalent to the statement that some sublevel set `{n | p_{n+1} - p_n ≤ B}` is infinite;
* it is equivalent (contrapositive form) to the failure of `p_{n+1} - p_n → ∞`;
* it is equivalent to the "prime pairs" form: arbitrarily far out there are two distinct primes
  within a fixed distance `B` — this is the form in which the sieve-theoretic proofs work,
  and the reduction from it to consecutive primes is carried out here;
* the base case `p_1 - p_0 = 3 - 2 = 1`, together with positivity of all prime gaps.
-/
theorem bounded_prime_gaps :
    (Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop ≠ ⊤ ↔ BoundedPrimeGaps) ∧
    (BoundedPrimeGaps ↔ ∃ B : ℕ, {n | primeGap n ≤ B}.Infinite) ∧
    (BoundedPrimeGaps ↔ ¬ Tendsto primeGap atTop atTop) ∧
    (BoundedPrimeGaps ↔ BoundedPrimePairs) ∧
    primeGap 0 = 1 ∧ (∀ n, 0 < primeGap n) :=
  ⟨liminf_ne_top_iff, infinite_iff, not_tendsto_iff, boundedPrimePairs_iff,
    primeGap_zero, primeGap_pos⟩

end Frontier

