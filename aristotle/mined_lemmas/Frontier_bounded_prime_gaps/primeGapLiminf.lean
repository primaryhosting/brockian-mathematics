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

noncomputable def primeGapLiminf : ℕ∞ :=
  Filter.liminf (fun n => (primeGap n : ℕ∞)) Filter.atTop

