/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Auxiliary bounded divisor check for `89`, decided by finite case analysis. -/
theorem divisors_89_bounded : ∀ m < 90, m ∣ 89 → m = 1 ∨ m = 89 := by decide

/--
**The prime `89` is a sum of two squares.**

The statement packages both facts: `89` is prime (it is greater than `1` and its only
divisors are `1` and itself), and `89 = 5 ^ 2 + 8 ^ 2`.

Note on the header: since a module doc comment must be the required first item of this file,
no `import` line may precede it, so the proof is developed self-containedly in core Lean.
(In Mathlib the primality is `by norm_num : Nat.Prime 89`, and the general two-squares fact for
primes `p % 4 ≠ 3` is `Nat.Prime.sq_add_sq`.)
-/
theorem two_squares_89 :
    (1 < 89 ∧ ∀ m : Nat, m ∣ 89 → m = 1 ∨ m = 89) ∧ ∃ a b : Nat, 89 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, fun m hm => ?_⟩, 5, 8, by decide⟩
  exact divisors_89_bounded m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

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

