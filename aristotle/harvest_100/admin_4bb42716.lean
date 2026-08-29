/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `IsPrimeNat p` says that `p` is a prime natural number: it is at least `2`
and its only divisors are `1` and itself.

(The required header of this file is a module docstring, which Lean requires to
come after any `import`; consequently this file is self-contained and does not
import Mathlib, so primality is spelled out here.) -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Only divisors of `29` below `30` are `1` and `29` — a finite check. -/
theorem divisors_29_bounded : ∀ d : Nat, d < 30 → d ∣ 29 → d = 1 ∨ d = 29 := by
  decide

/-- `29` is prime. -/
theorem isPrimeNat_29 : IsPrimeNat 29 := by
  refine ⟨by omega, fun d hd => ?_⟩
  have hle : d ≤ 29 := Nat.le_of_dvd (by omega) hd
  exact divisors_29_bounded d (by omega) hd

/-- The prime `29` is a sum of two squares: `29 = 2 ^ 2 + 5 ^ 2`. -/
theorem two_squares_29 : IsPrimeNat 29 ∧ ∃ a b : Nat, 29 = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_29, 2, 5, by decide⟩

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

