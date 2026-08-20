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

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian.AndricaConjecture

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/

lemma andricaAt_iff (n : ℕ) :
    AndricaAt n ↔ (nthPrime (n + 1) - nthPrime n - 1) ^ 2 < 4 * nthPrime n := by
  set a := nthPrime n with ha
  set b := nthPrime (n + 1) with hb
  have hapos : 0 < a := nthPrime_pos n
  have hareal : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
  have hsqrt_pos : 0 < Real.sqrt (a : ℝ) := Real.sqrt_pos.mpr hareal
  have hsq : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt hareal.le
  rw [AndricaAt, ← ha, ← hb, sqrt_sub_sqrt_lt_one_iff (by positivity) (by positivity)]
  rcases le_or_gt b (a + 1) with h | h
  · -- degenerate case: the arithmetic inequality is `0 < 4a`, and the analytic one holds too
    have h0 : b - a - 1 = 0 := by omega
    rw [h0]
    have hb' : (b : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast h
    constructor
    · intro _; simpa using hapos
    · intro _; nlinarith
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + k + 1 := ⟨b - a - 1, by omega⟩
    have hkb : b - a - 1 = k := by omega
    rw [hkb]
    have hbr : (b : ℝ) = (a : ℝ) + (k : ℝ) + 1 := by rw [hk]; push_cast; ring
    rw [hbr]
    constructor
    · intro h1
      have hk2 : (k : ℝ) ^ 2 < 4 * (a : ℝ) := by nlinarith
      exact_mod_cast hk2
    · intro h1
      have hk2 : (k : ℝ) ^ 2 < 4 * (a : ℝ) := by exact_mod_cast h1
      nlinarith

/-- The Andrica conjecture is *equivalent* to the purely arithmetic statement
`(p_{n+1} - p_n - 1)^2 < 4 * p_n` for all `n`. -/
