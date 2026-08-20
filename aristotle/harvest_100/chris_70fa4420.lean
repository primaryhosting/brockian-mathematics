/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, spelled out: `n` is at least `2` and its only
divisors are `1` and `n`. It is stated directly here because the required header
comment must be the very first thing in the file, which rules out any `import`
line, so `Nat.Prime` is not available. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

/-- Key intermediate lemma: every divisor of `29` that is at most `29`
is either `1` or `29`. -/
theorem divisors_of_29_le : ∀ m : Nat, m ≤ 29 → m ∣ 29 → m = 1 ∨ m = 29 := by decide

/-- `29` is prime. -/
theorem isPrimeNat_29 : IsPrimeNat 29 :=
  ⟨by omega, fun m hm => divisors_of_29_le m (Nat.le_of_dvd (by omega) hm) hm⟩

/-- Key intermediate lemma: `29` is the sum of the squares of `2` and `5`. -/
theorem twentynine_eq_sq_add_sq : (29 : Nat) = 2 ^ 2 + 5 ^ 2 := by decide

/-- The prime `29` is a sum of two squares. -/
theorem two_squares_29 : IsPrimeNat 29 ∧ ∃ a b : Nat, (29 : Nat) = a ^ 2 + b ^ 2 :=
  ⟨isPrimeNat_29, 2, 5, twentynine_eq_sq_add_sq⟩

end Math

#print axioms Math.two_squares_29

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

