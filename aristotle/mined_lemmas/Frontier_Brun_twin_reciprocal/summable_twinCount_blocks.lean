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

theorem summable_twinCount_blocks :
    Summable (fun N : ℕ => (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N) := by
  obtain ⟨c, N₀, hbound⟩ := exists_twinCount_block_bound
  have hg : Summable (fun N : ℕ => c * (((Nat.log 2 N : ℝ) + 1) ^ 2 / N ^ 2)) :=
    summable_log_sq_div_sq.mul_left c
  rw [← summable_nat_add_iff N₀]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_add_iff N₀).mpr hg)
  calc (twinCount (2 ^ (n + N₀ + 1)) : ℝ) / 2 ^ (n + N₀)
      ≤ c * ((Nat.log 2 (n + N₀) : ℝ) + 1) ^ 2 / (n + N₀ : ℕ) ^ 2 := hbound (n + N₀) (by omega)
    _ = c * (((Nat.log 2 (n + N₀) : ℝ) + 1) ^ 2 / (n + N₀ : ℕ) ^ 2) := by ring

/-- The twin primes in the dyadic block `[2^N, 2^(N+1))` contribute at most
`twinCount (2^(N+1)) / 2^N` to the sum of reciprocals. -/
