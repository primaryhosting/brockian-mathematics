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
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun p => if p = (0, 0) ∨ p = (1, 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 2-qubit GHZ state is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz2, Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff, Complex.norm_real,
    abs_of_nonneg, Real.sq_sqrt]
  norm_num

/-- The definition of `ghz2` indeed describes `(|00⟩ + |11⟩)/√2`. -/
theorem ghz2_eq : ghz2 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    (EuclideanSpace.single (0, 0) 1 + EuclideanSpace.single (1, 1) 1) := by
  ext p
  fin_cases p <;> simp [ghz2, EuclideanSpace.single_apply, Prod.ext_iff]

end QC

#print axioms QC.ghz2_normalized

