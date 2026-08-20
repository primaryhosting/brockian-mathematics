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
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Finset Complex

variable {n : ℕ}

/-- The inner product `⟨ψ|φ⟩` of two (finite dimensional) state vectors,
antilinear in the first argument. -/

noncomputable def hadamardAncilla (v : Fin 2 × Fin n × Fin n → ℂ) :
    Fin 2 × Fin n × Fin n → ℂ :=
  fun p => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
    (v (0, p.2) + (if p.1 = 0 then 1 else -1) * v (1, p.2))

/-- The controlled swap (Fredkin) gate: the two registers are exchanged when the
ancilla qubit is `|1⟩`. -/
