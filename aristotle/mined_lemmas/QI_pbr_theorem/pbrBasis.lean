/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

/-! ### Two-qubit vectors, inner products and the states involved -/

/-- A (pure) qubit state vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit state vector, written in curried form. -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- The product (tensor) of two qubit vectors. -/

noncomputable def pbrBasis : Fin 4 → TwoQubit :=
  ![ ![![0, (s2 : ℂ)], ![(s2 : ℂ), 0]],
     ![![1 / 2, -(1 / 2)], ![1 / 2, 1 / 2]],
     ![![1 / 2, 1 / 2], ![-(1 / 2), 1 / 2]],
     ![![(s2 : ℂ), 0], ![0, -(s2 : ℂ)]] ]

/-! ### The quantum input: the PBR basis is orthonormal and antidistinguishes -/

/-- The four PBR vectors form an orthonormal basis of the two-qubit space, so they
do describe a genuine projective measurement. -/
