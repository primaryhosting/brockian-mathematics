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

theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [ghz2, PiLp.toLp_apply]
  rw [show (Finset.univ : Finset (Fin 2 → Fin 2)) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} from by
    decide]
  norm_num [Finset.sum_insert, Fin.forall_fin_two]

end QC

