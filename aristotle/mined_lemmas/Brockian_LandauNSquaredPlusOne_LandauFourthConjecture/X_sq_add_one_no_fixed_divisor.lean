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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean does not allow a module
-- docstring to precede the `import` commands; the text is otherwise verbatim.)

import Mathlib

/-!
# Landau Fourth Conjecture

Landau's fourth problem asks whether there are infinitely many primes of the form `n ^ 2 + 1`.
This is a well-known open problem, so what is proved here is:

* `LandauFourthConjecture` : a **conditional** reduction — Bunyakovsky's conjecture
  (in the form `BunyakovskyHypothesis`) implies Landau's fourth conjecture
  (`LandauFourthStatement`).  All the hypotheses of Bunyakovsky's conjecture are verified
  unconditionally for the polynomial `X ^ 2 + 1`.
* `X_sq_add_one_irreducible` : `X ^ 2 + 1` is irreducible over `ℤ`.
* `infinite_setOf_prime_dvd_sq_add_one` : an **unconditional** partial result — infinitely many
  primes divide some number of the form `n ^ 2 + 1`.
* `infinite_setOf_large_prime_factor` : an **unconditional** partial result — for infinitely many
  `n`, the number `n ^ 2 + 1` has a prime factor exceeding `2 * n`.
-/

open Polynomial

namespace Brockian.LandauNSquaredPlusOne

/-- **Landau's fourth conjecture**: there are infinitely many natural numbers `n` such that
`n ^ 2 + 1` is prime. -/

theorem X_sq_add_one_no_fixed_divisor (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : ℤ[X]).eval (n : ℤ)) := by
  refine ⟨0, fun h => ?_⟩
  simp only [Nat.cast_zero, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at h
  rw [show ((0 : ℤ) ^ 2 + 1) = ((1 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

/-- The values of `X ^ 2 + 1` at natural numbers are exactly the numbers `n ^ 2 + 1`, and
primality over `ℤ` matches primality over `ℕ`. -/
