/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
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

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector of the Hilbert space
`EuclideanSpace ℂ (Fin 2 → Fin 2)`, whose index set is the set of 2-bit strings:
the amplitude is `1/√2` on the strings `00` and `11`, and `0` elsewhere. -/

noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 → Fin 2) :=
  WithLp.toLp 2 (fun b : Fin 2 → Fin 2 =>
    if (∀ i, b i = 0) ∨ (∀ i, b i = 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The GHZ state is indeed `(|00⟩ + |11⟩)/√2`, written in terms of the standard
basis vectors `EuclideanSpace.single`. -/
