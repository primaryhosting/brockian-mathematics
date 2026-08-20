/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 13 is a sum of two squares.**

Since the required file header is a module doc comment, which Lean requires to be the very
first item of a file (no `import` may follow it), this file is developed without imports.
Primality of `13` is therefore spelled out explicitly: `13 ≠ 1` and every divisor of `13`
is either `1` or `13`. The two-squares decomposition is `13 = 2 ^ 2 + 3 ^ 2`. -/

theorem two_squares_13 :
    (13 ≠ 1 ∧ ∀ d : Nat, d ∣ 13 → d = 1 ∨ d = 13) ∧ ∃ a b : Nat, 13 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, fun d hd => ?_⟩, 2, 3, by decide⟩
  have hle : d ≤ 13 := Nat.le_of_dvd (by decide) hd
  have hall : ∀ e : Nat, e ≤ 13 → e ∣ 13 → e = 1 ∨ e = 13 := by decide
  exact hall d hle hd

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

