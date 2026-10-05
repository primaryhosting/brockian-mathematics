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
/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is wrapped in an outer block comment because Lean 4 requires
-- `import` commands to precede every other command, including module docstrings.)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
Whether there are infinitely many even perfect numbers is an open problem (it is equivalent
to the infinitude of Mersenne primes).  What is proved here is exactly that equivalence, i.e.
a Lean-checked reduction of the conjecture:

  `{n | Even n ∧ n.Perfect}.Infinite ↔ {p | (mersenne p).Prime}.Infinite`

The proof goes through the Euclid–Euler theorem: the map `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`
is a bijection from the set of Mersenne exponents `p` with `2 ^ p - 1` prime onto the set of
even perfect numbers.
-/

namespace Brockian.MersennePerfect

open Set

/-- The set of exponents `p` for which `mersenne p = 2 ^ p - 1` is prime. -/

theorem euclidMap_lt_euclidMap {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    euclidMap a < euclidMap b := by
  have h1 : (2 : ℕ) ^ (a - 1) ≤ 2 ^ (b - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : mersenne a < mersenne b := by
    have : (2 : ℕ) ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
    have h2a : 1 ≤ (2 : ℕ) ^ a := Nat.one_le_two_pow
    simp only [mersenne]
    omega
  have hpos : 0 < (2 : ℕ) ^ (b - 1) := Nat.two_pow_pos _
  exact Nat.mul_lt_mul_of_le_of_lt h1 h2 hpos

/-- `euclidMap` is injective on the set of Mersenne exponents. -/
