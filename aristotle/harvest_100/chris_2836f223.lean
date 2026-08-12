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

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the complex Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)` (one `Fin 2` factor per qubit). -/
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p => if p = (0, 0) ∨ p = (1, 1) then (1 : ℂ) / Real.sqrt 2 else 0

@[simp] lemma ghz2_apply (p : Fin 2 × Fin 2) :
    ghz2 p = if p = (0, 0) ∨ p = (1, 1) then (1 : ℂ) / Real.sqrt 2 else 0 := rfl

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2` is a unit vector.

The proof rewrites the norm with `EuclideanSpace.norm_eq` (`‖x‖ = √(∑ i, ‖x i‖ ^ 2)`)
and evaluates the resulting four-term sum. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz2, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

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

