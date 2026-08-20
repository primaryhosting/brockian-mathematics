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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter UniqueFactorizationMonoid
open scoped Nat

namespace Brockian.BrocardProblem

/-- The `abc` conjecture, stated for natural numbers, using the radical
`UniqueFactorizationMonoid.radical` (the product of the distinct prime factors):
for every `ε > 0` there is a constant `K > 0` such that whenever `a + b = c` with
`a, b` positive and coprime, we have `c ≤ K * rad(a * b * c) ^ (1 + ε)`. -/

lemma finite_of_factorial_le (C B : ℝ) (hC : 0 < C) :
    {n : ℕ | (n ! : ℝ) ≤ C * B ^ n}.Finite := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop |B|
  have h2 : ∀ᶠ n : ℕ in atTop, |B| ^ n / (n ! : ℝ) < 1 / C := by
    have := h.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / C by positivity))
    simpa using this
  obtain ⟨N, hN⟩ := h2.exists_forall_of_atTop
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hlt
  simp only [Set.mem_Iio, not_lt] at hlt
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h3 := hN n hlt
  rw [div_lt_div_iff₀ hfac hC] at h3
  have habs : C * B ^ n ≤ C * |B| ^ n := by
    have hb : B ^ n ≤ |B| ^ n := (le_abs_self _).trans (by rw [abs_pow])
    nlinarith
  nlinarith

/-- The unconditional determination of all solutions of Brocard's problem with `n ≤ 7`:
they are exactly `n = 4, 5, 7` (with `m = 5, 11, 71`). -/
