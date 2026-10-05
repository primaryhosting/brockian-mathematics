import Brockian.MersennePerfect

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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: written as a plain block comment rather than a module docstring, since Lean 4
requires `import` commands to precede any module docstring.)
-/

import Mathlib

namespace Brockian.MersennePerfect

open Finset

/-- The set of exponents `p` for which the Mersenne number `2 ^ p - 1` is prime. -/

theorem mersenne_infinite_of_evenPerfects_infinite (h : EvenPerfects.Infinite) :
    MersennePrimeExponents.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨n, hn, hnN⟩ := h.exists_gt (2 ^ (2 * N + 2))
  obtain ⟨k, hkp, rfl⟩ := even_perfect_eq_two_pow_mul_mersenne hn.1 hn.2
  refine ⟨k + 1, hkp, ?_⟩
  by_contra hcon
  have hkN : k + 1 ≤ N := by omega
  have hub : 2 ^ k * mersenne (k + 1) < 2 ^ (2 * k + 1) := by
    have h1 : mersenne (k + 1) < 2 ^ (k + 1) := by
      simp only [mersenne]
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    calc 2 ^ k * mersenne (k + 1) < 2 ^ k * 2 ^ (k + 1) := by gcongr
      _ = 2 ^ (2 * k + 1) := by rw [← pow_add]; ring_nf
  have hmono : (2 : ℕ) ^ (2 * k + 1) ≤ 2 ^ (2 * N + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Sanity checks: `6` and `28` are even perfect numbers. -/
example : 6 ∈ EvenPerfects :=
  ⟨by decide, by rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]; decide⟩

example : 28 ∈ EvenPerfects :=
  ⟨by decide, by rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]; decide⟩

example : 2 ∈ MersennePrimeExponents := by
  show (mersenne 2).Prime
  norm_num [mersenne]

/-- **Euclid–Euler reduction.** There are infinitely many even perfect numbers if and only if
there are infinitely many Mersenne primes. -/
