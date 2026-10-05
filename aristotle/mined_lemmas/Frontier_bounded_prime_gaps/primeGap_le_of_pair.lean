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
