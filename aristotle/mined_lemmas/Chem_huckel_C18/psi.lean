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

set_option grind.warning false

namespace Chem

open Matrix

/-- The standard additive character `x ↦ exp (2 π i x / 18)` on `ZMod 18`. -/

noncomputable def psi : AddChar (ZMod 18) ℂ := ZMod.stdAddChar

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertex set viewed as `ZMod 18`
(which is definitionally `Fin 18`). -/
