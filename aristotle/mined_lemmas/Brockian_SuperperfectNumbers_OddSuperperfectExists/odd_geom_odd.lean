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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ (σ n) = 2 n`.  Suryanarayana and Kanold
showed that the even superperfect numbers are exactly the powers `2 ^ k` with
`2 ^ (k + 1) - 1` prime; whether an *odd* superperfect number exists is an open problem.

This file contains a Lean-checked reduction of that open problem, together with the
(easy half of the) even classification and two unconditional constraints on a
hypothetical odd superperfect number.
-/

open scoped ArithmeticFunction.sigma

open ArithmeticFunction Finset

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

private lemma odd_geom_odd {p : ℕ} (hp : Odd p) {m : ℕ} (hm : Even m) :
    Odd (∑ i ∈ range (m + 1), p ^ i) := by
  have h : (∑ i ∈ range (m + 1), p ^ i) % 2 = (∑ i ∈ range (m + 1), (p ^ i % 2)) % 2 :=
    Finset.sum_nat_mod _ _ _
  have h2 : ∀ i ∈ range (m + 1), p ^ i % 2 = 1 := fun i _ => Nat.odd_iff.mp hp.pow
  rw [Finset.sum_congr rfl h2] at h
  simp at h
  obtain ⟨t, rfl⟩ := hm
  rw [Nat.odd_iff, h]
  omega

/-- If every odd prime occurs to an even power in `m`, then `σ m` is odd.  (Equivalently:
`σ m` is odd exactly when `m` is a square or twice a square.) -/
