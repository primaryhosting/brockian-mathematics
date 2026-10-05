/-!
# Two Squares 17
Category: Pure Mathematics
Target: Math.two_squares_17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **17 is a prime that is a sum of two squares.**

The first conjunct says that `17` is prime (it is at least `2` and its only divisors are
`1` and `17`); the second exhibits it as a sum of two squares, `17 = 1 ^ 2 + 4 ^ 2`.

Primality is spelled out elementarily here so that the requested header comment can be the
very first thing in the file (Lean requires `import` commands to precede any module
docstring).  The file `RequestProject/TwoSquares17Mathlib.lean` derives the same statement
phrased with Mathlib's `Nat.Prime`. -/
theorem two_squares_17 :
    (2 ≤ 17 ∧ ∀ m : Nat, m ∣ 17 → m = 1 ∨ m = 17) ∧ ∃ a b : Nat, 17 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 4, by decide⟩
  intro m hm
  have hle : m ≤ 17 := Nat.le_of_dvd (by decide) hm
  have hall : ∀ k : Nat, k < 18 → k ∣ 17 → k = 1 ∨ k = 17 := by decide
  exact hall m (by omega) hm

end Math

import Mathlib
import RequestProject.TwoSquares17

/-!
# Two Squares 17 (Mathlib phrasing)

Restatement of `Math.two_squares_17` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `17` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
theorem two_squares_17_prime : Nat.Prime 17 ∧ ∃ a b : ℕ, 17 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_17.2⟩

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

