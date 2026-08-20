import Mathlib

/-!
# Two Squares 97 — Mathlib version

Companion to `RequestProject/TwoSquares97.lean`.  Here the statement is phrased
with Mathlib's `Nat.Prime` and derived from the general Mathlib theorem
`Nat.Prime.sq_add_sq` (Fermat's two-squares theorem: a prime `p` with
`p % 4 ≠ 3` is a sum of two squares).
-/

namespace Math

/-- `97` is prime and is a sum of two squares, via `Nat.Prime.sq_add_sq`. -/
theorem two_squares_97_mathlib : Nat.Prime 97 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 97 := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact ⟨by norm_num, Nat.Prime.sq_add_sq (by norm_num)⟩

/-- The explicit witness: `97 = 4 ^ 2 + 9 ^ 2`. -/
theorem two_squares_97_explicit : (97 : ℕ) = 4 ^ 2 + 9 ^ 2 := by norm_num

end Math

/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, stated without any external dependency
(so that this file can begin with the required header comment, which Lean
does not allow to precede `import` commands). -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- `97` is prime. -/
theorem isPrimeNat_97 : IsPrimeNat 97 := by
  refine ⟨by decide, ?_⟩
  have h : ∀ m < 98, m ∣ 97 → m = 1 ∨ m = 97 := by decide
  intro m hm
  exact h m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

/-- **Two squares for 97.** The prime `97` is a sum of two squares:
`97 = 4 ^ 2 + 9 ^ 2`. -/
theorem two_squares_97 : IsPrimeNat 97 ∧ ∃ a b : Nat, 97 = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_97, 4, 9, rfl⟩

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

