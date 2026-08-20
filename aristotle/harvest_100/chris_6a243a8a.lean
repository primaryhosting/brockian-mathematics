import Mathlib

/-!
# Two Squares 13 — Mathlib companion

A Mathlib-based restatement of `Math.two_squares_13`, obtained from the general
Fermat two-squares theorem `Nat.Prime.sq_add_sq` (every prime `p` with `p % 4 ≠ 3`
is a sum of two squares).
-/

namespace Math

/-- `13` is prime and is a sum of two squares, via Mathlib's `Nat.Prime.sq_add_sq`. -/
theorem two_squares_13_mathlib : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine ⟨by norm_num, ?_⟩
  obtain ⟨a, b, h⟩ := Nat.Prime.sq_add_sq (p := 13) (by norm_num)
  exact ⟨a, b, h.symm⟩

end Math

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`.

We also record that `13` is prime, in the elementary form that `1 < 13` and every divisor
of `13` is either `1` or `13`.

(The header comment required for this file must be the very first thing in the file, and Lean
forbids `import` commands after a comment, so this development is written using only Lean's
core library rather than Mathlib; the proof is fully self-contained and axiom-clean.) -/
theorem two_squares_13 :
    (1 < 13 ∧ ∀ m : Nat, m ∣ 13 → m = 1 ∨ m = 13) ∧ ∃ a b : Nat, 13 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, ?_⟩, 2, 3, rfl⟩
  have key : ∀ m < 14, m ∣ 13 → m = 1 ∨ m = 13 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hm)) hm

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

