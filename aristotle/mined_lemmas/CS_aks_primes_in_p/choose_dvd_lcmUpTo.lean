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


theorem choose_dvd_lcmUpTo (M : ℕ) : (2 * M).choose M ∣ lcmUpTo (2 * M) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hL : lcmUpTo (2 * M) ≠ 0 := lcmUpTo_ne_zero _
  have hC : (2 * M).choose M ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [← Nat.factorization_le_iff_dvd hC hL]
  intro q
  by_cases hq : q.Prime
  · haveI : Fact q.Prime := ⟨hq⟩
    have h1 : q ^ ((2 * M).choose M).factorization q ≤ 2 * M :=
      Nat.pow_factorization_choose_le (by omega)
    have h2 : q ^ ((2 * M).choose M).factorization q ∣ lcmUpTo (2 * M) :=
      dvd_lcmUpTo (Nat.one_le_pow _ _ hq.pos) h1
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq hL).1 h2
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

