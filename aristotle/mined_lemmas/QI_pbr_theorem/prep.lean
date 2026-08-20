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

noncomputable def prep : Fin 4 → Qubit × Qubit :=
  ![(ket0, ket0), (ket0, ketPlus), (ketPlus, ket0), (ketPlus, ketPlus)]

/-- The Pusey–Barrett–Rudolph measurement basis:
`(|01⟩+|10⟩)/√2`, `(|0-⟩+|1+⟩)/√2`, `(|+1⟩+|-0⟩)/√2`, `(|+-⟩+|-+⟩)/√2`. -/
