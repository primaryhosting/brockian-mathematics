/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, spelled out: `n` is at least `2` and its only
divisors are `1` and `n`.  (This is definitionally the same notion as
`Nat.Prime`; it is stated here directly because the required file header must be
the very first thing in the file, which precludes an `import` command.) -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

/-- Every divisor of `89` is `1` or `89`. -/
theorem divisors_89 : ∀ m : Nat, m ∣ 89 → m = 1 ∨ m = 89 := by
  have key : ∀ m < 90, m ∣ 89 → m = 1 ∨ m = 89 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

/-- The prime `89` is a sum of two squares: `89 = 5 ^ 2 + 8 ^ 2`. -/
theorem two_squares_89 : IsPrimeNat 89 ∧ ∃ a b : Nat, 89 = a ^ 2 + b ^ 2 :=
  ⟨⟨by decide, divisors_89⟩, 5, 8, by decide⟩

end Math

import Mathlib

/-!
# Two Squares 89 (Mathlib formulation)

Companion to `RequestProject/TwoSquares89.lean`, stating the same result with
Mathlib's `Nat.Prime`.  The target file itself cannot import Mathlib, since its
required header comment must precede every command in the file.
-/

namespace Math

/-- The prime `89` is a sum of two squares: `89 = 5 ^ 2 + 8 ^ 2`. -/
theorem two_squares_89_mathlib : Nat.Prime 89 ∧ ∃ a b : ℕ, 89 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 5, 8, by norm_num⟩

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

