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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- The finite set of *Goldbach representations* of `n`: those `p ≤ n` such that both `p`
and `n - p` are prime. -/

theorem exists_two_primes_of_reps_nonempty {n : ℕ} (h : (reps n).Nonempty) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, hp⟩ := h
  simp only [reps, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp
  exact ⟨p, n - p, hp.2.1, hp.2.2, Nat.add_sub_cancel' hp.1⟩

/-- A *Hardy–Littlewood style lower-bound model* for the Goldbach representation counting
function beyond a threshold: a constant `c > 0` and a threshold `bound ≥ 4` such that every
even `n ≥ bound` has at least `c * n / (log n)^2` representations as a sum of two primes.

This is the "model" hypothesis of the schema; the theorem
`goldbach_beyond_of_model` turns it into the Goldbach conclusion beyond `bound`. -/
structure Model where
  /-- Threshold beyond which the lower bound is asserted. -/
  bound : ℕ
  /-- The implied constant of the lower bound. -/
  const : ℝ
  /-- The threshold is at least `4`. -/
  bound_ge : 4 ≤ bound
  /-- The implied constant is positive. -/
  const_pos : 0 < const
  /-- The counting lower bound, valid for every even `n` beyond the threshold. -/
  lower : ∀ n : ℕ, bound ≤ n → Even n →
    const * (n : ℝ) / (Real.log n) ^ 2 ≤ ((reps n).card : ℝ)

/-- For `4 ≤ n` the analytic lower bound `c * n / (log n)^2` is strictly positive. -/
