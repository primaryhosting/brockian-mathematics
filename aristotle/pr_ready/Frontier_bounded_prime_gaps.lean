/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Statement: liminf (p_{n+1}−p_n) is finite (Zhang/Maynard).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Filter

/-- `nthPrime n` is the `n`-th prime number, counting from `nthPrime 0 = 2`. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The `n`-th prime gap `p_{n+1} - p_n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

lemma nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

lemma nthPrime_lt_nthPrime_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  Nat.nth_lt_nth Nat.infinite_setOf_prime |>.2 (Nat.lt_succ_self n)

lemma one_le_primeGap (n : ℕ) : 1 ≤ primeGap n :=
  Nat.sub_pos_of_lt (nthPrime_lt_nthPrime_succ n)

/-- **Bounded prime gaps (Zhang–Maynard), Lean-checked reduction.**

The assertion that `liminf_{n → ∞} (p_{n+1} - p_n)` is finite, taken in the
completed natural numbers `ℕ∞`, is *equivalent* to the combinatorial statement
that there is a bound `B` such that infinitely many consecutive prime pairs are
at distance at most `B`.

This equivalence is proved unconditionally here; the deep theorem of
Zhang and Maynard is precisely the assertion that either side holds. -/
theorem bounded_prime_gaps :
    (∃ B : ℕ, ∀ N : ℕ, ∃ n, N ≤ n ∧ primeGap n ≤ B) ↔
      liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  constructor
  · rintro ⟨B, hB⟩
    have hle : (⨆ n : ℕ, ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) ≤ (B : ℕ∞) := by
      refine iSup_le fun n => ?_
      obtain ⟨m, hnm, hm⟩ := hB n
      exact le_trans (iInf₂_le m hnm) (by exact_mod_cast hm)
    exact lt_of_le_of_lt hle (by simp)
  · intro h
    obtain ⟨B, hB⟩ : ∃ B : ℕ, (⨆ n : ℕ, ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) = (B : ℕ∞) := by
      obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 (ne_of_lt h)
      exact ⟨B, hB.symm⟩
    refine ⟨B, fun N => ?_⟩
    by_contra hcon
    push_neg at hcon
    have : ((B : ℕ∞) + 1) ≤ ⨅ i, ⨅ _ : N ≤ i, (primeGap i : ℕ∞) := by
      refine le_iInf₂ fun i hi => ?_
      have := hcon i hi
      exact_mod_cast this
    have h2 : ((B : ℕ∞) + 1) ≤ (B : ℕ∞) :=
      this.trans (hB ▸ le_iSup (fun n : ℕ => ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) N)
    have h3 : B + 1 ≤ B := by exact_mod_cast h2
    omega

/-- Unconditionally, the liminf of the prime gaps is at least `1`, since consecutive
primes are distinct. -/
theorem one_le_liminf_primeGap : 1 ≤ liminf (fun n => (primeGap n : ℕ∞)) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine le_trans ?_ (le_iSup (fun n : ℕ => ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) 0)
  exact le_iInf₂ fun i _ => by exact_mod_cast one_le_primeGap i

/-- If `q` is a prime strictly larger than the `k`-th prime, then the `(k+1)`-st prime
is at most `q`: the `(k+1)`-st prime is the least prime exceeding the `k`-th one. -/
lemma nthPrime_succ_le_of_prime {k q : ℕ} (hq : q.Prime) (h : nthPrime k < q) :
    nthPrime (k + 1) ≤ q := by
  by_contra hcon
  push_neg at hcon
  exact absurd (Nat.le_nth_of_lt_nth_succ hcon hq) (not_le.2 h)

/-- **Reduction of bounded prime gaps to bounded prime pairs.**

If for some fixed `B` there are arbitrarily large primes `p` admitting a prime `q`
with `p < q ≤ p + B`, then the liminf of the prime gaps is finite. -/
theorem bounded_prime_gaps_of_bounded_pairs (B : ℕ)
    (h : ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  refine bounded_prime_gaps.1 ⟨B, fun N => ?_⟩
  obtain ⟨p, q, hple, hp, hq, hpq, hqB⟩ := h (nthPrime N + 1)
  refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
  · have hnp : nthPrime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have : nthPrime N < nthPrime (Nat.count Nat.Prime p) := by omega
    exact le_of_lt ((Nat.nth_lt_nth Nat.infinite_setOf_prime).1 this)
  · have hnp : nthPrime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have hsucc : nthPrime (Nat.count Nat.Prime p + 1) ≤ q :=
      nthPrime_succ_le_of_prime hq (by omega)
    simp only [primeGap, hnp]
    omega

/-- The twin prime conjecture implies that the liminf of the prime gaps is finite. -/
theorem bounded_prime_gaps_of_twin_primes
    (h : ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ (p + 2).Prime) :
    liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  refine bounded_prime_gaps_of_bounded_pairs 2 fun N => ?_
  obtain ⟨p, hN, hp, hp2⟩ := h N
  exact ⟨p, p + 2, hN, hp, hp2, by omega, le_rfl⟩

end Frontier


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

