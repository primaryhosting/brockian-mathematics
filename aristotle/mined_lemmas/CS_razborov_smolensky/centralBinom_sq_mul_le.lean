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
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/

lemma centralBinom_sq_mul_le (k : ℕ) : (Nat.centralBinom k) ^ 2 * (2 * k + 1) ≤ 16 ^ k := by
  induction k with
  | zero => simp [Nat.centralBinom]
  | succ k ih =>
    have hrec := Nat.succ_mul_centralBinom_succ k
    have hpos : 0 < (k + 1) ^ 2 := by positivity
    have key : ((Nat.centralBinom (k + 1)) ^ 2 * (2 * (k + 1) + 1)) * (k + 1) ^ 2
        ≤ 16 ^ (k + 1) * (k + 1) ^ 2 := by
      have e1 : (Nat.centralBinom (k + 1)) ^ 2 * (k + 1) ^ 2
          = (2 * (2 * k + 1)) ^ 2 * (Nat.centralBinom k) ^ 2 := by
        have : ((k + 1) * Nat.centralBinom (k + 1)) ^ 2
            = (2 * (2 * k + 1) * Nat.centralBinom k) ^ 2 := by rw [hrec]
        calc (Nat.centralBinom (k + 1)) ^ 2 * (k + 1) ^ 2
            = ((k + 1) * Nat.centralBinom (k + 1)) ^ 2 := by ring
          _ = (2 * (2 * k + 1) * Nat.centralBinom k) ^ 2 := this
          _ = (2 * (2 * k + 1)) ^ 2 * (Nat.centralBinom k) ^ 2 := by ring
      have e2 : ((Nat.centralBinom (k + 1)) ^ 2 * (2 * (k + 1) + 1)) * (k + 1) ^ 2
          = (2 * (2 * k + 1)) ^ 2 * (2 * k + 3) * (Nat.centralBinom k) ^ 2 := by
        calc ((Nat.centralBinom (k + 1)) ^ 2 * (2 * (k + 1) + 1)) * (k + 1) ^ 2
            = ((Nat.centralBinom (k + 1)) ^ 2 * (k + 1) ^ 2) * (2 * k + 3) := by ring
          _ = ((2 * (2 * k + 1)) ^ 2 * (Nat.centralBinom k) ^ 2) * (2 * k + 3) := by rw [e1]
          _ = (2 * (2 * k + 1)) ^ 2 * (2 * k + 3) * (Nat.centralBinom k) ^ 2 := by ring
      rw [e2]
      have e3 : (2 * (2 * k + 1)) ^ 2 * (2 * k + 3) * (Nat.centralBinom k) ^ 2
          = (4 * (2 * k + 1) * (2 * k + 3)) * ((Nat.centralBinom k) ^ 2 * (2 * k + 1)) := by
        ring
      rw [e3]
      have e4 : (4 * (2 * k + 1) * (2 * k + 3)) * ((Nat.centralBinom k) ^ 2 * (2 * k + 1))
          ≤ (4 * (2 * k + 1) * (2 * k + 3)) * 16 ^ k := Nat.mul_le_mul_left _ ih
      refine le_trans e4 ?_
      have e5 : 4 * (2 * k + 1) * (2 * k + 3) ≤ 16 * (k + 1) ^ 2 := by nlinarith
      calc (4 * (2 * k + 1) * (2 * k + 3)) * 16 ^ k
          ≤ (16 * (k + 1) ^ 2) * 16 ^ k := Nat.mul_le_mul_right _ e5
        _ = 16 ^ (k + 1) * (k + 1) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right key hpos

/-- Half of the binomial coefficients of an odd row sum to `4 ^ m`. -/
