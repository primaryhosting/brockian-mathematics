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
Note: the header block above is written as a plain block comment rather than a module docstring
(`/-! ... -/`) because Lean requires `import` commands to precede every other command, including
module docstrings.

## Contents

* `sqrt_sub_sqrt_lt_one_of_sq_gap_le` : the elementary estimate `√b - √a < 1` for `a < b`
  with `(b - a)^2 ≤ 4a`.
* `sqrt_sub_sqrt_lt_one_iff` : the Andrica inequality is equivalent to the gap bound.
* `AndricaConjecture` : Andrica's conjecture, conditional on the prime-gap bound
  `(p_{n+1} - p_n)^2 ≤ 4 p_n`.  (Andrica's conjecture itself is an open problem.)
* `andrica_first_ten` : unconditional verification for the first ten prime gaps.
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`). -/

theorem sqrt_sub_sqrt_lt_one_of_sq_gap_le {a b : ℕ} (hab : a < b)
    (h : (b - a) ^ 2 ≤ 4 * a) : Real.sqrt b - Real.sqrt a < 1 := by
  set x := Real.sqrt a with hx
  set y := Real.sqrt b with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxy : x < y := by
    have hlt : (a : ℝ) < b := by exact_mod_cast hab
    exact Real.sqrt_lt_sqrt (by positivity) hlt
  have hxsq : x ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hysq : y ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
    have := Nat.cast_sub (le_of_lt hab) (R := ℝ)
    simpa using this
  have h' : ((b : ℝ) - a) ^ 2 ≤ 4 * (a : ℝ) := by
    have hc := (Nat.cast_le (α := ℝ)).2 h
    rw [Nat.cast_pow, hcast, Nat.cast_mul] at hc
    simpa using hc
  have hgap : (b : ℝ) - a ≤ 2 * x := by
    nlinarith [hx0, hxsq]
  have hexp : (y - x) * (y + x) = (b : ℝ) - a := by
    have hfac : (y - x) * (y + x) = y ^ 2 - x ^ 2 := by ring
    rw [hfac, hxsq, hysq]
  have hpos : 0 < y + x := by linarith
  nlinarith [hexp, hgap, hpos, hxy]

/-- The Andrica inequality for a pair is *equivalent* to the corresponding gap bound. -/
