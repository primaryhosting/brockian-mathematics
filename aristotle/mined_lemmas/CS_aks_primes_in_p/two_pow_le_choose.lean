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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem two_pow_le_choose (d : ℕ) : 2 ^ d ≤ (2 * d).choose d := by
  induction d with
  | zero => simp
  | succ k ih =>
      have hstep : 2 * ((2 * k).choose k) ≤ (2 * (k + 1)).choose (k + 1) := by
        have h1 : (2 * k + 1 + 1).choose (k + 1) =
            (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) := Nat.choose_succ_succ _ _
        have h2 : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) := by
          have := Nat.choose_symm (n := 2 * k + 1) (k := k) (by omega)
          rw [show 2 * k + 1 - k = k + 1 by omega] at this
          exact this.symm
        have h3 : (2 * k + 1).choose (k + 1) = (2 * k).choose k + (2 * k).choose (k + 1) :=
          Nat.choose_succ_succ _ _
        have h4 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
        rw [h4, h1]
        omega
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ 2 * ((2 * k).choose k) := by omega
        _ ≤ (2 * (k + 1)).choose (k + 1) := hstep

/-- If `n` is not a power of `p`, the numbers `n ^ i * p ^ j` are pairwise distinct. -/
