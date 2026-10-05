/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires every `import` command to appear before any other
syntax in a file, including module doc comments.  Since the header comment above must
be the very first thing in this file, this file is deliberately import-free and the
statement below is phrased and proved using only the Lean 4 core library.

A Mathlib-based companion proof of the same fact, using Mathlib's Fermat two-squares
theorem `Nat.Prime.sq_add_sq`, is given in `RequestProject/TwoSquares89Mathlib.lean`.
-/

namespace Math

/-- **The prime `89` is a sum of two squares.**

`89` is prime (it is at least `2` and its only divisors are `1` and `89`), and
`89 = 5 ^ 2 + 8 ^ 2`. -/
theorem two_squares_89 :
    (2 ≤ 89 ∧ ∀ m : Nat, m ∣ 89 → m = 1 ∨ m = 89) ∧ ∃ a b : Nat, a ^ 2 + b ^ 2 = 89 := by
  refine ⟨⟨by decide, ?_⟩, 5, 8, rfl⟩
  have hall : ∀ m < 90, m ∣ 89 → m = 1 ∨ m = 89 := by decide
  intro m hm
  exact hall m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

import Mathlib

/-!
# Two Squares 89 — Mathlib companion

Mathlib-based version of `Math.two_squares_89`: the prime `89` is a sum of two squares.
The key Mathlib lemma is `Nat.Prime.sq_add_sq` (Fermat's two-squares theorem): a prime
`p` with `p % 4 ≠ 3` is a sum of two squares.
-/

namespace Math

/-- `89` is prime and is a sum of two squares, with the explicit witness `89 = 5 ^ 2 + 8 ^ 2`. -/
theorem two_squares_89_mathlib : Nat.Prime 89 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 89 :=
  ⟨by norm_num, 5, 8, by norm_num⟩

/-- The same existence statement derived from Mathlib's two-squares theorem
`Nat.Prime.sq_add_sq`, applied to the prime `89` (which satisfies `89 % 4 = 1 ≠ 3`). -/
theorem two_squares_89_via_sq_add_sq : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 89 := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 89) (by norm_num)

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

