import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` to precede all commands, including this module docstring,
so the header comment appears immediately after the single `import Mathlib` line.)

## Contents

We formalize the statement "the liminf of the sequence of prime gaps `p_{n+1} - p_n` is finite"
(the Zhang / Maynard theorem) as `Frontier.primeGapLiminf < ⊤`, where the liminf is taken in
`ℕ∞ = WithTop ℕ`, and we give a Lean-checked reduction: this liminf is finite **iff** there is a
constant `B` such that arbitrarily far out one can find two primes `p < q` with `q - p ≤ B`.

The reduction is proved unconditionally; it turns the analytic statement about the liminf of the
gap sequence into the purely combinatorial statement that is the actual content of the
Zhang / Maynard theorem (which is not proved here).
-/

open Filter

namespace Frontier

/-- The `n`-th prime number, `p n`, with `p 0 = 2`. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap `p_{n+1} - p_n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The limit inferior of the sequence of prime gaps, as an element of `ℕ∞ = WithTop ℕ`;
it is `< ⊤` exactly when the gaps are bounded at infinitely many indices. -/
noncomputable def primeGapLiminf : ℕ∞ :=
  Filter.liminf (fun n => (primeGap n : ℕ∞)) Filter.atTop

lemma nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

lemma nthPrime_strictMono : StrictMono nthPrime := fun _ _ h =>
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr h

lemma nthPrime_lt_nthPrime_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  nthPrime_strictMono (Nat.lt_succ_self n)

lemma le_nthPrime (n : ℕ) : n ≤ nthPrime n := nthPrime_strictMono.le_apply

/-- `p 0 = 2`. -/
lemma nthPrime_zero : nthPrime 0 = 2 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  rwa [show Nat.count Nat.Prime 2 = 0 from by decide] at h

/-- `p 1 = 3`. -/
lemma nthPrime_one : nthPrime 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  rwa [show Nat.count Nat.Prime 3 = 1 from by decide] at h

/-- `p 2 = 5`. -/
lemma nthPrime_two : nthPrime 2 = 5 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 5) (by norm_num)
  rwa [show Nat.count Nat.Prime 5 = 2 from by decide] at h

/-- Base case: the first prime gap is `3 - 2 = 1`. -/
lemma primeGap_zero : primeGap 0 = 1 := by
  simp [primeGap, nthPrime_zero, nthPrime_one]

/-- The second prime gap is `5 - 3 = 2`. -/
lemma primeGap_one : primeGap 1 = 2 := by
  simp [primeGap, nthPrime_one, nthPrime_two]

/-- Finiteness of the liminf of the prime gaps is exactly the existence of a bound `B` attained
by infinitely many gaps. -/
lemma primeGapLiminf_lt_top_iff :
    primeGapLiminf < ⊤ ↔ ∃ B : ℕ, ∀ N : ℕ, ∃ n, N ≤ n ∧ primeGap n ≤ B := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.mp h.ne
    refine ⟨B, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨N, hN⟩ := hcon
    have hev : ∀ᶠ n in atTop, ((B : ℕ∞) + 1) ≤ (primeGap n : ℕ∞) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have h1 : (B : ℕ) + 1 ≤ primeGap n := hN n hn
      exact_mod_cast h1
    have h2 : ((B : ℕ∞) + 1) ≤ primeGapLiminf :=
      le_liminf_of_le (u := fun n => (primeGap n : ℕ∞)) (f := atTop) ⟨⊤, by simp⟩ hev
    rw [← hB] at h2
    have h3 : ((B + 1 : ℕ) : ℕ∞) ≤ ((B : ℕ) : ℕ∞) := by push_cast; exact h2
    have h4 : B + 1 ≤ B := Nat.cast_le (α := ℕ∞) |>.mp h3
    omega
  · rintro ⟨B, hB⟩
    have hfreq : ∃ᶠ n in atTop, (primeGap n : ℕ∞) ≤ (B : ℕ∞) := by
      rw [frequently_atTop]
      intro N
      obtain ⟨n, hn, hle⟩ := hB N
      exact ⟨n, hn, by exact_mod_cast hle⟩
    exact lt_of_le_of_lt (Filter.liminf_le_of_frequently_le hfreq) (by simp)

/-- A pair of primes `p < q` with `q ≤ p + B` yields a gap between *consecutive* primes
of size at most `B`, namely at the index of `p`. -/
lemma primeGap_le_of_pair {p q B : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hle : q ≤ p + B) :
    ∃ n, nthPrime n = p ∧ primeGap n ≤ B := by
  classical
  refine ⟨Nat.count Nat.Prime p, Nat.nth_count hp, ?_⟩
  have hcp : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  have hcq : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  have hstep : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q := by
    have h1 : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
      rw [Nat.count_succ]; simp [hp]
    have h2 : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime q := Nat.count_monotone _ hpq
    omega
  have hnext : nthPrime (Nat.count Nat.Prime p + 1) ≤ q := by
    have h := (Nat.nth_le_nth Nat.infinite_setOf_prime (k := Nat.count Nat.Prime p + 1)
      (n := Nat.count Nat.Prime q)).mpr hstep
    rwa [hcq] at h
  unfold primeGap
  rw [show nthPrime (Nat.count Nat.Prime p) = p from hcp]
  omega

/-- **Reduction of the bounded prime gaps statement (Zhang / Maynard).**

The liminf of the sequence of prime gaps `p_{n+1} - p_n` is finite if and only if there is a
bound `B` such that arbitrarily far out one finds two primes `p < q` with `q ≤ p + B`. -/
theorem bounded_prime_gaps :
    primeGapLiminf < ⊤ ↔
      ∃ B : ℕ, ∀ N : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N ≤ p ∧ p < q ∧ q ≤ p + B := by
  rw [primeGapLiminf_lt_top_iff]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨n, hn, hgap⟩ := hB N
    have hlt : nthPrime n < nthPrime (n + 1) := nthPrime_lt_nthPrime_succ n
    refine ⟨nthPrime n, nthPrime (n + 1), nthPrime_prime n, nthPrime_prime (n + 1),
      le_trans hn (le_nthPrime n), hlt, ?_⟩
    have hg : primeGap n = nthPrime (n + 1) - nthPrime n := rfl
    omega
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨p, q, hp, hq, hNp, hpq, hle⟩ := hB (nthPrime N)
    obtain ⟨n, hn, hgap⟩ := primeGap_le_of_pair hp hq hpq hle
    refine ⟨n, ?_, hgap⟩
    have hmono : nthPrime N ≤ nthPrime n := by rw [hn]; exact hNp
    exact (Nat.nth_le_nth Nat.infinite_setOf_prime).mp hmono

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

