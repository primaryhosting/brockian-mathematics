/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: the required header above is a module docstring, and Lean does not
allow `import` commands after it, so this file is deliberately self-contained and uses no
imports.  Primality of `37` is therefore spelled out directly (`37 ≥ 2` and every divisor
of `37` is `1` or `37`) instead of via `Nat.Prime`.
-/

namespace Math

/-- `IsPrimeNat n` says that `n` is a prime natural number: it is at least `2` and its only
divisors are `1` and itself.  This is the standard definition, spelled out here because the
file has no imports. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- `37` is prime. -/
theorem isPrimeNat_37 : IsPrimeNat 37 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have h : d ≤ 37 := Nat.le_of_dvd (by decide) hd
  have hlt : d < 38 := by omega
  revert hd hlt
  revert d
  decide

/-- **Two squares for 37**: the prime `37` is a sum of two squares, namely `37 = 1 ^ 2 + 6 ^ 2`. -/
theorem two_squares_37 : IsPrimeNat 37 ∧ ∃ a b : Nat, 37 = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_37, 1, 6, rfl⟩

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

