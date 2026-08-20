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
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-! ## The quantum ingredients

We work with two qubits, i.e. with `ℂ⁴` indexed by `Fin 4`, where the index `2*a + b`
stands for the product basis vector `|a⟩ ⊗ |b⟩`.
-/

/-- The inner product on `ℂ⁴` (conjugate-linear in the first argument). -/

noncomputable def phi : Fin 2 → Fin 2 → (Fin 4 → ℂ)
  | 0, 0 => ![1, 0, 0, 0]
  | 0, 1 => ![rt, rt, 0, 0]
  | 1, 0 => ![rt, 0, rt, 0]
  | 1, 1 => ![1/2, 1/2, 1/2, 1/2]

/-- The four vectors of the entangled PBR measurement:
`ξ₀ = (|0⟩|1⟩+|1⟩|0⟩)/√2`, `ξ₁ = (|0⟩|−⟩+|1⟩|+⟩)/√2`,
`ξ₂ = (|+⟩|1⟩+|−⟩|0⟩)/√2`, `ξ₃ = (|+⟩|−⟩+|−⟩|+⟩)/√2`. -/
