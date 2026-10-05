import Mathlib

/-!
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in `EuclideanSpace ℂ (Fin 2 × Fin 2)`
(the basis vector indexed by `(i, j)` is `|ij⟩`). -/

theorem ghz2_eq : ghz2 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    (EuclideanSpace.single (0, 0) 1 + EuclideanSpace.single (1, 1) 1) := by
  ext p
  fin_cases p <;> simp [ghz2, EuclideanSpace.single_apply, Prod.ext_iff]

end QC

#print axioms QC.ghz2_normalized

