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
# Two Squares 53
Category: Pure Mathematics
Target: Math.two_squares_53
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 53.** The number `53` is prime (stated elementarily: it is at least `2`
and its only divisors are `1` and itself) and it is a sum of two squares, namely
`53 = 2 ^ 2 + 7 ^ 2`.

The statement is phrased without `Mathlib`'s `Nat.Prime` because the required header comment
must be the very first thing in the file, which precludes any `import` command. -/
theorem two_squares_53 :
    (2 ≤ 53 ∧ ∀ d : Nat, d ∣ 53 → d = 1 ∨ d = 53) ∧ ∃ a b : Nat, 53 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, ?_⟩, 2, 7, by decide⟩
  intro d hd
  have hle : d ≤ 53 := Nat.le_of_dvd (by omega) hd
  have hall : ∀ d < 54, d ∣ 53 → d = 1 ∨ d = 53 := by decide
  exact hall d (by omega) hd

end Math

