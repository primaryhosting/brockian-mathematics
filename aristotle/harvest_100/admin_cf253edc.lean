import Mathlib
import RequestProject.TwoSquares13

/-
# Two Squares 13 — Mathlib version

Companion to `RequestProject/TwoSquares13.lean`.  (That file must literally begin with the
prescribed module-doc header, and Lean 4 does not allow `import` commands after a doc comment,
so the Mathlib-based development lives here.)

The relevant Mathlib result is `Nat.Prime.sq_add_sq` (Mathlib/NumberTheory/SumTwoSquares.lean):
for a prime `p` with `p % 4 ≠ 3` there are naturals `a b` with `a ^ 2 + b ^ 2 = p`.
-/

namespace Math

/-- `13` is prime, in Mathlib's sense. -/
theorem thirteen_prime_mathlib : Nat.Prime 13 := by norm_num

/-- Existence of a two-square representation of `13`, obtained from Mathlib's
`Nat.Prime.sq_add_sq` (Fermat's two-squares theorem) rather than by exhibiting `2` and `3`. -/
theorem two_squares_13_via_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 13 :=
  haveI : Fact (Nat.Prime 13) := ⟨thirteen_prime_mathlib⟩
  Nat.Prime.sq_add_sq (p := 13) (by decide)

/-- The explicit statement `Math.two_squares_13`, restated with `Nat.Prime`. -/
theorem two_squares_13_prime : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 :=
  ⟨thirteen_prime_mathlib, two_squares_13⟩

end Math

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 13.** The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`. -/
theorem two_squares_13 : ∃ a b : Nat, 13 = a ^ 2 + b ^ 2 := ⟨2, 3, rfl⟩

/-- `13` is indeed prime: it is at least `2` and its only divisors are `1` and `13`. -/
theorem thirteen_prime : 2 ≤ 13 ∧ ∀ m : Nat, m ∣ 13 → m = 1 ∨ m = 13 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hle : m < 14 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)
  have key : ∀ k : Nat, k < 14 → k ∣ 13 → k = 1 ∨ k = 13 := by decide
  exact key m hle hm

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

