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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.LandauNSquaredPlusOne

open Polynomial

/-- Landau's fourth problem: there are infinitely many primes of the form `n ^ 2 + 1`,
phrased as "for every bound `N` there is some `n > N` with `n ^ 2 + 1` prime". -/

theorem exists_dvd_sq_add_one_of_prime_modEq_one {p : ℕ} (hp : p.Prime) (h : p ≡ 1 [MOD 4]) :
    ∃ n : ℕ, p ∣ n ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp4 : p % 4 ≠ 3 := by
    have : p % 4 = 1 % 4 := h
    omega
  obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hp4
  refine ⟨y.val, ?_⟩
  have : ((y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    have : y ^ 2 = -1 := by rw [hy]; ring
    rw [this]
    ring
  exact (ZMod.natCast_eq_zero_iff _ p).mp this

/-- **Unconditional partial result.** Infinitely many primes divide some number of the
form `n ^ 2 + 1`. -/
