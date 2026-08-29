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

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

/-- **Oppermann's conjecture** (open): for every `n ≥ 2` there is a prime strictly between
`n²` and `n² + n`, and a prime strictly between `n² + n` and `(n+1)²`. -/

lemma sqrt_sub_sqrt_lt_one {p q m : ℕ} (hm : m * m ≤ p) (h : q < p + 2 * m + 1) :
    Real.sqrt q - Real.sqrt p < 1 := by
  have hp0 : (0:ℝ) ≤ (p : ℝ) := by positivity
  have hmp : (m : ℝ) ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by positivity) hp0]
    have : ((m * m : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hm
    push_cast at this
    nlinarith
  have hpos : (0:ℝ) < Real.sqrt p + 1 := by positivity
  have hlt : Real.sqrt q < Real.sqrt p + 1 := by
    rw [Real.sqrt_lt' hpos]
    have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hp0
    have hq : (q : ℝ) < (p : ℝ) + 2 * m + 1 := by exact_mod_cast h
    nlinarith
  linarith

/-- A prime is never of the form `m * k` with `2 ≤ m` and `m < m * k`. -/
