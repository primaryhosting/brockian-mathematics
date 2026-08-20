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

noncomputable def swapTestFinal (ψ φ : Fin n → ℂ) : Fin 2 × Fin n × Fin n → ℂ :=
  hadamardAncilla (cswap (hadamardAncilla (inputState ψ φ)))

/-- The probability that the swap test accepts, i.e. that measuring the ancilla
qubit of the final state returns `0`. -/
