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

theorem no_fixed_prime_divisor (p : ℕ) (hp : p.Prime) :
    ∃ m : ℕ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : Polynomial ℤ).eval (m : ℤ)) := by
  refine ⟨0, ?_⟩
  simp only [eval_X_sq_add_one]
  norm_num
  intro hdvd
  have : p ∣ 1 := by exact_mod_cast hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- **Conditional reduction of Landau's fourth problem.**
Bunyakovsky's conjecture implies that there are infinitely many primes of the form
`n ^ 2 + 1`. -/
