/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 → Fin 2)` whose basis vectors are indexed by 2-bit strings. -/
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 → Fin 2) :=
  WithLp.toLp 2 (fun b : Fin 2 → Fin 2 =>
    if (∀ i, b i = 0) ∨ (∀ i, b i = 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2` is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [show (Finset.univ : Finset (Fin 2 → Fin 2)) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} from by
    decide]
  norm_num [ghz2]

end QC

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

