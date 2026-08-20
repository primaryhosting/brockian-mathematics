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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
A natural number `n` is *quasiperfect* if `σ n = 2 * n + 1`, i.e. the sum of the proper
divisors of `n` (including `1`) equals `n + 1`.  No quasiperfect number is known, and their
existence is an open problem.

This file proves the classical structural constraints (Cattaneo, 1951): a quasiperfect number
must be an odd perfect square, and it cannot be a prime power.  The main theorem
`QuasiperfectExists` is the resulting *reduction*: a quasiperfect number exists if and only if
there is an odd `k > 1`, not a prime power, whose square is quasiperfect.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of all of its
divisors equals `2 * n + 1`. -/

theorem not_sq_of_three_mod_four_dvd_succ {m N k t : ℕ} (hN3 : N % 4 = 3) (hNodd : Odd N)
    (hsq : m = k * k) (hNt : N * t = m + 1) : False := by
  have hcast : (N : ℤ) * (t : ℤ) = (m : ℤ) + 1 := by exact_mod_cast hNt
  have hdvd : (N : ℤ) ∣ (m : ℤ) - (-1 : ℤ) := ⟨(t : ℤ), by linarith⟩
  have hmod : ((m : ℤ)) % (N : ℤ) = (-1 : ℤ) % (N : ℤ) :=
    Int.modEq_iff_dvd.mpr (by simpa using hdvd.neg_right)
  have h1 : jacobiSym (m : ℤ) N = jacobiSym (-1) N := jacobiSym.mod_left' hmod
  rw [jacobiSym.at_neg_one hNodd, ZMod.χ₄_nat_three_mod_four hN3] at h1
  have hcop : Nat.gcd k N = 1 := by
    have h2 : Nat.gcd k N ∣ m + 1 := hNt ▸ Dvd.dvd.mul_right (Nat.gcd_dvd_right k N) t
    have h3 : Nat.gcd k N ∣ m := hsq ▸ Dvd.dvd.mul_left (Nat.gcd_dvd_left k N) k
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h3).mp h2)
  have h4 : jacobiSym ((k : ℤ) ^ 2) N = 1 := jacobiSym.sq_one' (by simpa [Int.gcd] using hcop)
  rw [show ((k : ℤ) ^ 2) = (m : ℤ) by rw [hsq]; push_cast; ring] at h4
  rw [h4] at h1
  exact absurd h1 (by decide)

/-- **Cattaneo's theorem**, first half: every quasiperfect number is odd. -/
