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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BrocardProblem

open Nat

set_option maxRecDepth 100000

/-- The statement of Brocard's conjecture: the only natural numbers `n` for which
`n! + 1` is a perfect square are `n = 4`, `n = 5` and `n = 7`
(with `4! + 1 = 5²`, `5! + 1 = 11²`, `7! + 1 = 71²`). -/

theorem pronic_of_factorial_succ_sq {n m : ℕ} (hn : 2 ≤ n) (h : n ! + 1 = m ^ 2) :
    ∃ a : ℕ, n ! = 4 * a * (a + 1) := by
  have hdvd : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
  have hmodd : ¬ 2 ∣ m := by
    intro hm
    have h2 : (2 : ℕ) ∣ m ^ 2 := dvd_pow hm two_ne_zero
    rw [← h] at h2
    omega
  have hmod : m % 2 = 1 := by omega
  obtain ⟨a, ha⟩ := Nat.odd_iff.2 hmod
  refine ⟨a, ?_⟩
  subst ha
  have hexp : (2 * a + 1) ^ 2 = 4 * a * (a + 1) + 1 := by ring
  rw [hexp] at h
  exact Nat.add_right_cancel h

/-- Conversely, if `n! = 4a(a+1)` then `n! + 1 = (2a+1)²` is a square. -/
