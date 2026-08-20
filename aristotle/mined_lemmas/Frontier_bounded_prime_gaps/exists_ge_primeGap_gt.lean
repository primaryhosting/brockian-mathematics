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

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(with `p_0 = 2`). -/

theorem exists_ge_primeGap_gt (B N : ℕ) : ∃ n ≥ N, B < primeGap n := by
  obtain ⟨n, hn⟩ := exists_primeGap_gt (B + (Finset.range N).sup primeGap)
  refine ⟨n, ?_, by omega⟩
  by_contra hlt
  push_neg at hlt
  have : primeGap n ≤ (Finset.range N).sup primeGap :=
    Finset.le_sup (Finset.mem_range.mpr hlt)
  omega

/-- Consequently the `limsup` of the prime gaps is infinite: the `liminf` formulation is the
correct way to state bounded gaps. -/
