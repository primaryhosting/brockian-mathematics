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

theorem exists_log_poly_bound (a b : ℕ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, a * (Nat.log 2 N + 1) ^ b ≤ N := by
  obtain ⟨m₀, hm₀⟩ := exists_pow_bound a b
  refine ⟨2 ^ m₀, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by norm_num)) hN
  set m := Nat.log 2 N with hm
  have hmm : m₀ ≤ m := Nat.le_log_of_pow_le (by norm_num) hN
  have h1 : a * (m + 1) ^ b ≤ a * (m + 2) ^ b :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) b)
  exact h1.trans ((hm₀ m hmm).trans (Nat.pow_log_le_self 2 hNpos.ne'))

/-- The final combination step in the dyadic block estimate: given the four bounds for the
terms of Brun's sieve inequality, the block bound follows. -/
