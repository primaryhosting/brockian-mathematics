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

import Mathlib

namespace Brockian.AndricaConjecture

open Real

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`). -/

theorem andricaGap_lt_one_of_sq_gap_le (n : ℕ)
    (h : (nthPrime (n + 1) - nthPrime n) ^ 2 ≤ 4 * nthPrime n) :
    andricaGap n < 1 := by
  set d : ℕ := nthPrime (n + 1) - nthPrime n with hd
  have hlt := nthPrime_lt_succ n
  have hsum : (nthPrime (n + 1) : ℝ) = (nthPrime n : ℝ) + (d : ℝ) := by
    have : nthPrime n + d = nthPrime (n + 1) := by omega
    exact_mod_cast this.symm
  have hR : (d : ℝ) ^ 2 ≤ 4 * (nthPrime n : ℝ) := by exact_mod_cast h
  have hdle : (d : ℝ) ≤ 2 * Real.sqrt (nthPrime n) := by
    have hs : Real.sqrt (nthPrime n) ^ 2 = (nthPrime n : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg ((nthPrime n : ℝ)), Nat.cast_nonneg (α := ℝ) d]
  rw [andricaGap_lt_one_iff, hsum]
  linarith

/-- **Unconditional sufficient criterion, small-gap form.** If `p_n ≥ 4` and the `n`-th prime
gap is at most `4`, the Andrica inequality holds at `n`. -/
