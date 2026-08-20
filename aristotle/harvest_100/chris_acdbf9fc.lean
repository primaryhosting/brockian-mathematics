/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in `EuclideanSpace ℂ (Fin 2 × Fin 2)`:
the basis vector indexed by `(i, j)` corresponds to the computational basis state `|ij⟩`. -/
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p : Fin 2 × Fin 2 =>
    if p = (0, 0) ∨ p = (1, 1) then (1 : ℂ) / Real.sqrt 2 else 0

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2` is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [EuclideanSpace.norm_eq]
  have key : ∀ p : Fin 2 × Fin 2, ‖ghz2 p‖ ^ 2 =
      if p = (0, 0) ∨ p = (1, 1) then (1 / 2 : ℝ) else 0 := by
    intro p
    by_cases hp : p = (0, 0) ∨ p = (1, 1)
    · have hval : ghz2 p = (1 : ℂ) / Real.sqrt 2 := by simp [ghz2, hp]
      rw [hval, norm_div, div_pow, if_pos hp]
      simp [Complex.norm_real, abs_of_pos hs, h2]
    · have hval : ghz2 p = 0 := by simp [ghz2, hp]
      rw [hval, if_neg hp]
      simp
  simp only [key, Fintype.sum_prod_type, Fin.sum_univ_two]
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

