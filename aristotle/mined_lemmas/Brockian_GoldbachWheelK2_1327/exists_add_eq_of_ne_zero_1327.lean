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

namespace Brockian

/-- The new wheel modulus `1327` is prime. -/

theorem exists_add_eq_of_ne_zero_1327 (r : ZMod 1327) :
    ∃ a b : ZMod 1327, a ≠ 0 ∧ b ≠ 0 ∧ a + b = r := by
  by_cases h : r = 1
  · refine ⟨2, -1, ?_, ?_, ?_⟩
    · decide
    · decide
    · subst h; ring
  · refine ⟨1, r - 1, ?_, ?_, by ring⟩
    · decide
    · intro hb
      exact h (by linear_combination hb)

/-- **Goldbach wheel for the modulus `1327`, `K = 2`.**

Sums of two primes cover *every* residue class modulo the wheel modulus `1327`, and this
remains true if both primes are required to exceed an arbitrary bound `N`: for every
`r : ZMod 1327` and every `N : ℕ` there are primes `p, q > N` with `p + q ≡ r [MOD 1327]`. -/
