/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open NormedSpace

namespace Frontier

section

variable {A : Type*} [CStarAlgebra A]

/-- A `ℚ`-normed-algebra structure, obtained by restricting scalars from `ℂ`; it is needed
to talk about `NormedSpace.exp` in a C⋆-algebra. -/
noncomputable local instance normedAlgebraRatOfCStarAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

/-- `exp (t • H)` commutes with `H`. -/

lemma exp_neg_smul_mul_exp_smul (H : A) (t : ℝ) :
    exp ((-t) • H) * exp (t • H) = 1 := by
  simpa using exp_smul_mul_exp_neg_smul H (-t)

/-- If `H` is anti-self-adjoint then `exp (t • H)` is unitary. -/
