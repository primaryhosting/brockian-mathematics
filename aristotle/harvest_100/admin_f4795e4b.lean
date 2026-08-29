import Mathlib
import RequestProject.TwoSquares97

/-!
# Two Squares 97 (Mathlib phrasing)

Restatement of `Math.two_squares_97` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `97` is a sum of two squares: `97 = 9 ^ 2 + 4 ^ 2`. -/
theorem two_squares_97_prime : Nat.Prime 97 ∧ ∃ a b : ℕ, 97 = a ^ 2 + b ^ 2 := by
  obtain ⟨-, ha⟩ := Math.two_squares_97
  exact ⟨by norm_num, ha⟩

end Math

/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command in a file,
-- so this file (whose first characters are fixed by the required header comment above)
-- cannot import Mathlib. The statement below is therefore phrased with a self-contained
-- definition of primality. The file `TwoSquares97Mathlib.lean` restates the result with
-- Mathlib's `Nat.Prime`.

namespace Math

/-- `97` is prime (every divisor is `1` or `97`, and `97 ≥ 2`) and it is a sum of two
squares: `97 = 9 ^ 2 + 4 ^ 2`. -/
theorem two_squares_97 :
    (2 ≤ 97 ∧ ∀ m : Nat, m ∣ 97 → m = 1 ∨ m = 97) ∧ ∃ a b : Nat, 97 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 9, 4, by decide⟩
  have key : ∀ m < 97, m ∣ 97 → m = 1 := by decide
  intro m hm
  rcases Nat.lt_or_ge m 97 with h | h
  · exact Or.inl (key m h hm)
  · exact Or.inr (Nat.le_antisymm (Nat.le_of_dvd (by decide) hm) h)

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

