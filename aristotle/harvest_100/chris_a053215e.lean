import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 (Mathlib `Nat.Prime` form)

A restatement of `Math.two_squares_5` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- `5` is prime (in Mathlib's sense) and is a sum of two squares. -/
theorem two_squares_5_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, (5 : ℕ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 2, by norm_num⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `5` is a sum of two squares.

Primality of `5` is spelled out directly (`2 ≤ 5` and every divisor of `5` is `1` or `5`),
so that the file can begin with the required header comment (a Lean file may not have any
command, including `import`, before its module docstring); the witnesses are `5 = 1 ^ 2 + 2 ^ 2`. -/
theorem two_squares_5 :
    (2 ≤ 5 ∧ ∀ m : Nat, m ∣ 5 → m = 1 ∨ m = 5) ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 2, by decide⟩
  have hall : ∀ m < 6, m ∣ 5 → m = 1 ∨ m = 5 := by decide
  intro m hm
  exact hall m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

#print axioms Math.two_squares_5

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

