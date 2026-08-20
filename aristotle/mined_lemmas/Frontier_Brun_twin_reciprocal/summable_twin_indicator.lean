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
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

theorem summable_twin_indicator :
    Summable (Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun n => (1 : ℝ) / n)) := by
  classical
  set f := Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun n => (1 : ℝ) / n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    Set.indicator_nonneg (fun a _ => by positivity) n
  refine summable_of_sum_range_le (c := ∑' N, (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N)
    hf0 (fun n => ?_)
  have hmaps : ∀ i ∈ Finset.range n, Nat.log 2 i ∈ Finset.range n := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    exact lt_of_le_of_lt (Nat.log_le_self 2 i) hi
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  calc ∑ N ∈ Finset.range n, ∑ i ∈ Finset.range n with Nat.log 2 i = N, f i
      ≤ ∑ N ∈ Finset.range n, (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N :=
        Finset.sum_le_sum fun N _ => sum_indicator_block_le n N
    _ ≤ ∑' N, (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N :=
        Summable.sum_le_tsum _ (fun i _ => by positivity) summable_twinCount_blocks

end Brun

import Mathlib

/-!
# Products over primes

Two estimates over the primes `p ≤ z`:

* `Brun.prod_odd_one_sub_two_div_le`: `∏_{2 < p ≤ z} (1 - 2/p) ≤ 4 / (log z)^2`, which follows
  from the elementary Euler-product bound `∏_{p ≤ z} (1 - 1/p)⁻¹ ≥ ∑_{n ≤ z} 1/n ≥ log z`.
* `Brun.exists_prod_one_add_bound`: `∏_{p ≤ z} (1 + 4/p) ≤ C (log z)^A` for suitable constants,
  a consequence of Chebyshev's bound `primorial n ≤ 4^n` (a Mertens-type estimate).
-/

open Finset

namespace Brun

/-- The completely multiplicative function `n ↦ 1/n`, as a monoid homomorphism. -/
