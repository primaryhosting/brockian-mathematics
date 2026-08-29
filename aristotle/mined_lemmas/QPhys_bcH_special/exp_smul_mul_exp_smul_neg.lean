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
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- written as a plain block comment; the module docstring below repeats it.)

import Mathlib

/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NormedSpace

namespace QPhys

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `ℚ`-algebra structure obtained by restricting scalars from `ℝ`; needed to use the
Mathlib API for the exponential in a Banach algebra. -/
noncomputable local instance ratAlgebraOfReal : NormedAlgebra ℚ 𝔸 :=
  NormedAlgebra.restrictScalars ℚ ℝ 𝔸

/-- `exp (t • X)` and `exp (t • (-X))` are inverse to each other. -/

theorem exp_smul_mul_exp_smul_neg (X : 𝔸) (t : ℝ) : exp (t • X) * exp (t • (-X)) = 1 := by
  rw [← exp_add_of_commute ((((Commute.refl X).neg_right).smul_left t).smul_right t)]
  simp

/-- If the commutator `C = AB - BA` commutes with `A`, then
`exp (t • A) * B = (B + t • C) * exp (t • A)`; equivalently `exp(tA) B exp(-tA) = B + t C`. -/
