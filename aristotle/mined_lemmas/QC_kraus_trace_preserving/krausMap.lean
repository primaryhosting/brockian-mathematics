/-
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- A quantum channel in Kraus form, `ρ ↦ ∑ k, E k * ρ * (E k)ᴴ`. -/

noncomputable def krausMap {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (E : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, E k * ρ * (E k)ᴴ

/-- **Kraus maps are trace preserving.**  If the Kraus operators `E k` satisfy the
completeness relation `∑ k, (E k)ᴴ * (E k) = 1`, then the induced map
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace of `ρ`. -/
