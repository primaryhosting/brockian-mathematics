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

lemma norm_conj_exp' {H : A} (hH : star H = -H) (t : ℝ) (x : A) :
    ‖exp ((-t) • H) * x * exp (t • H)‖ = ‖x‖ := by
  simpa using norm_conj_exp hH (-t) x

/-- **Key intermediate lemma (Lieb–Robinson estimate for the backwards evolution).**
The commutator of `a` with the backwards-evolved `b` moves away from its initial value
at most linearly in time, with speed controlled by `‖⁅b, H⁆‖`. -/
