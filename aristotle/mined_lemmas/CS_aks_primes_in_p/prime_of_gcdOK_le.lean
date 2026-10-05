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


theorem prime_of_gcdOK_le {n r : ℕ} (hn : 2 ≤ n) (hnr : n ≤ r)
    (h : ∀ a, 2 ≤ a → a ≤ r → Nat.gcd a n = 1 ∨ Nat.gcd a n = n) : n.Prime := by
  rw [Nat.prime_def_lt]
  refine ⟨hn, fun m hm hmn => ?_⟩
  by_contra hm1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd hmn) (by omega)
  have hgcd : Nat.gcd m n = m := Nat.gcd_eq_left hmn
  rcases h m (by omega) (by omega) with h1 | h1 <;> omega

