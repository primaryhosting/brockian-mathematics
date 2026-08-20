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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Brockian.AndricaConjecture

open scoped Nat

/-! ## The sequence of primes -/

/-- The set of primes is infinite. -/

theorem andrica_of_gap_le_two_mul (n k : ℕ) (hk : k ^ 2 ≤ nthPrime n)
    (h : nthPrime (n + 1) ≤ nthPrime n + 2 * k) :
    Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 := by
  rw [andrica_iff_gap]
  have hcast : (nthPrime (n + 1) : ℝ) ≤ (nthPrime n : ℝ) + 2 * (k : ℝ) := by exact_mod_cast h
  have hkr : (k : ℝ) ≤ Real.sqrt (nthPrime n) := by
    rw [show ((k : ℕ) : ℝ) = Real.sqrt (((k : ℕ) : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  linarith

/-- **Unconditional partial result.** Andrica's inequality holds at every index `n`
whose prime gap satisfies `p_{n+1} - p_n ≤ 2⌊√p_n⌋`. -/
