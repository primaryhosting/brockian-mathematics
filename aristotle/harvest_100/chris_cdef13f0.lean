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

/-!
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 73.**  `73` is prime — here primality is spelled out directly as
`1 < 73` together with the fact that every natural divisor of `73` is `1` or `73` — and it is
a sum of two squares, namely `73 = 3 ^ 2 + 8 ^ 2`.

The file is stated with no imports (the required header comment must be the first thing in the
file, which precludes an `import` line), so primality is written out explicitly rather than via
`Nat.Prime`; the two formulations are the same statement. -/
theorem two_squares_73 :
    (1 < 73 ∧ ∀ m : Nat, m ∣ 73 → m = 1 ∨ m = 73) ∧ ∃ a b : Nat, 73 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 3, 8, by decide⟩
  have key : ∀ m < 74, m ∣ 73 → m = 1 ∨ m = 73 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

#print axioms Math.two_squares_73

