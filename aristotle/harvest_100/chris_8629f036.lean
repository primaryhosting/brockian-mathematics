import Mathlib
import RequestProject.TwoSquares13

/-!
# Two Squares 13 — Mathlib restatement

A restatement of `Math.two_squares_13` using Mathlib's `Nat.Prime`.
(The main file `RequestProject/TwoSquares13.lean` is import-free, since its required
header comment must be the very first thing in the file.)
-/

namespace Math

/-- The prime `13` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
theorem two_squares_13_prime : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_13.2⟩

end Math

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `13` is prime, spelled out elementarily: it is at least `2`, and every divisor of it
is either `1` or `13`. -/
theorem thirteen_prime : 2 ≤ 13 ∧ ∀ m : Nat, m ∣ 13 → m = 1 ∨ m = 13 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hlt : m < 14 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)
  have key : ∀ k, k < 14 → k ∣ 13 → k = 1 ∨ k = 13 := by decide
  exact key m hlt hm

/-- The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`. -/
theorem two_squares_13 :
    (2 ≤ 13 ∧ ∀ m : Nat, m ∣ 13 → m = 1 ∨ m = 13) ∧ ∃ a b : Nat, 13 = a ^ 2 + b ^ 2 :=
  ⟨thirteen_prime, 2, 3, by decide⟩

end Math

#print axioms Math.two_squares_13

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

