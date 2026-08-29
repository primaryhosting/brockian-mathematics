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

import Mathlib
/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate Finset

namespace QC

variable {n : ℕ}

/-- A pure state of an `n`-level quantum register. -/
abbrev Reg (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A state of the full swap-test system: one ancilla qubit together with two
`n`-level registers.  We record it as its amplitude function. -/
abbrev SysState (n : ℕ) := Fin 2 × (Fin n × Fin n) → ℂ

/-- The Hadamard gate acting on the ancilla qubit. -/

noncomputable def hadAncilla (v : SysState n) : SysState n := fun p =>
  if p.1 = 0 then (v (0, p.2) + v (1, p.2)) / (Real.sqrt 2 : ℂ)
  else (v (0, p.2) - v (1, p.2)) / (Real.sqrt 2 : ℂ)

/-- The controlled-SWAP (Fredkin) gate: it swaps the two registers exactly when the
ancilla is in state `|1⟩`. -/
