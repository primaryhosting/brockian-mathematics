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

/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


noncomputable def amp {Y : Type*} [DecidableEq Y] (f : Vec n → Y) (y : Vec n) (z : Y) : ℂ :=
  (1 / 2 ^ n) * ∑ x : Vec n, chi (dot x y) * (if f x = z then 1 else 0)

/-- **Simon's interference identity.** If `y` is not orthogonal to the secret `s`,
then the amplitude of every outcome `(y, z)` vanishes: the measurement of the first
register always returns a vector orthogonal to `s`. -/
