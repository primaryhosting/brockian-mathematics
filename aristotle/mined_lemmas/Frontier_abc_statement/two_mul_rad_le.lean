/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-- The radical `rad n` of a natural number `n`: the product of the distinct primes
dividing `n`.  By convention `rad 0 = rad 1 = 1`. -/

theorem two_mul_rad_le {n : ℕ} (hn : 0 < n) (h : ¬ Squarefree n) : 2 * rad n ≤ n := by
  obtain ⟨d, hd⟩ := rad_dvd_self n
  have hr : 0 < rad n := Nat.pos_of_ne_zero (by
    rw [rad_eq_radical]; exact UniqueFactorizationMonoid.radical_ne_zero)
  have hd2 : 2 ≤ d := by
    by_contra hlt
    push_neg at hlt
    interval_cases d
    · omega
    · exact h (by
        rw [show n = rad n by omega, rad_eq_radical]
        exact UniqueFactorizationMonoid.squarefree_radical)
  calc 2 * rad n = rad n * 2 := by ring
    _ ≤ rad n * d := Nat.mul_le_mul_left _ hd2
    _ = n := hd.symm

/-! ### The finiteness form and the effective form of the conjecture are equivalent -/

