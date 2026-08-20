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

/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Finset Complex

variable {n : ℕ}

/-- The state of the swap-test register: one control qubit (`Fin 2`) together with two
`n`-dimensional systems, described by its amplitude function. -/
abbrev State (n : ℕ) := Fin 2 × Fin n × Fin n → ℂ

/-- Hadamard gate acting on the control qubit. -/

noncomputable def hadamardControl (v : State n) : State n := fun p =>
  if p.1 = 0 then (v (0, p.2) + v (1, p.2)) / (Real.sqrt 2 : ℝ)
  else (v (0, p.2) - v (1, p.2)) / (Real.sqrt 2 : ℝ)

/-- Controlled-SWAP gate: swaps the two `n`-dimensional systems when the control is `1`. -/
