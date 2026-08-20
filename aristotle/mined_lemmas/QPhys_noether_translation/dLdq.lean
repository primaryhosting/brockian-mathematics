/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
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

namespace QPhys

/-- The partial derivative `∂L/∂q` of a one-dimensional Lagrangian
`L : position → velocity → time → ℝ`. -/

noncomputable def dLdq (L : ℝ → ℝ → ℝ → ℝ) (q v t : ℝ) : ℝ := deriv (fun x => L x v t) q

/-- The partial derivative `∂L/∂v` of a one-dimensional Lagrangian
`L : position → velocity → time → ℝ`; evaluated along a trajectory this is the
canonical momentum. -/
