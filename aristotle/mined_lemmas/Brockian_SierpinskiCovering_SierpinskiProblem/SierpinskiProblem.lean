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

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This module is deliberately import-free (core Lean 4 only), because Lean does not
allow a module docstring to precede `import` commands.  A companion module
`Brockian.SierpinskiCoveringMathlib` imports Mathlib and restates the main result
using Mathlib's `Nat.Prime`.

Mathematical content: 78557 is a Sierpiński number, i.e. `78557 * 2 ^ n + 1` is
composite for every `n ≥ 1`.  The proof is the classical covering-congruence
argument: every residue class of `n` modulo 36 forces one of the primes
`3, 5, 7, 13, 19, 37, 73` to divide `78557 * 2 ^ n + 1`.
-/

namespace Brockian
namespace SierpinskiCovering

/-- Primality for naturals: `2 ≤ m` and the only divisors of `m` are `1` and `m`.
This is the usual notion; it is proved equivalent to Mathlib's `Nat.Prime` in the
companion module `Brockian.SierpinskiCoveringMathlib`. -/

theorem SierpinskiProblem : ∀ n : Nat, 1 ≤ n → ¬ IsPrimeNat (78557 * 2 ^ n + 1) := by
  intro n hn hprime
  have h := coverPrime_spec (n % 36) (Nat.mod_lt _ (by omega))
  have hp2 : 2 ≤ coverPrime (n % 36) := h.1
  have hp73 : coverPrime (n % 36) ≤ 73 := h.2.1
  have hdvd := coverPrime_dvd n
  have hbig : 73 < 78557 * 2 ^ n + 1 := by
    have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have := Nat.mul_le_mul_left 78557 h2
    omega
  rcases hprime.2 _ hdvd with h1 | h1 <;> omega

/-- Explicit compositeness: for `n ≥ 1` the number `78557 * 2 ^ n + 1` has a
divisor strictly between `1` and itself. -/
