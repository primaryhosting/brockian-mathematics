/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open Finset

/-- A (pure) state of an `n`-level quantum system is a unit vector in `ℂ^n`, i.e. a
function `Fin n → ℂ` whose squared amplitudes sum to `1`. -/

def prodState {n : ℕ} (psi phi : Fin n → ℂ) : Fin n × Fin n → ℂ := fun p => psi p.1 * phi p.2

/-- The SWAP operator on the two registers. -/
