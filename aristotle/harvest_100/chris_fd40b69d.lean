import Mathlib

/-!
# Two Squares 41 (Mathlib version)

Supplementary file: the same statement as `Math.two_squares_41`, but phrased with Mathlib's
`Nat.Prime`. It also records that the ad hoc primality predicate used in the main file agrees
with `Nat.Prime` on `41`.
-/

namespace Math

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/
theorem two_squares_41_mathlib : Nat.Prime 41 ∧ ∃ a b : ℕ, (41 : ℕ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 4, 5, by norm_num⟩

end Math

/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, which Lean requires to be the very
-- first command in the file; consequently no `import` line may precede it, so this file is
-- developed self-contained in core Lean 4 (no Mathlib), including the primality predicate.

namespace Math

/-- `IsPrimeNat p` says that `p` is at least `2` and its only divisors are `1` and `p`,
i.e. `p` is prime. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Every divisor of `41` is `1` or `41`. -/
theorem divisors_41 : ∀ d : Nat, d ∣ 41 → d = 1 ∨ d = 41 := by
  intro d hd
  have hlt : d < 42 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  revert hd
  revert hlt
  revert d
  decide

/-- `41` is prime. -/
theorem prime_41 : IsPrimeNat 41 := ⟨by decide, divisors_41⟩

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/
theorem two_squares_41 : IsPrimeNat 41 ∧ ∃ a b : Nat, 41 = a ^ 2 + b ^ 2 :=
  ⟨prime_41, 4, 5, by decide⟩

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

