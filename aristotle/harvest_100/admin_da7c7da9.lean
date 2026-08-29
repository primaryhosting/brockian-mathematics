import Mathlib

/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`, as a vector in the
`2 ^ 3 = 8`-dimensional complex Hilbert space, indexed so that `0` is `|000⟩`
and `7` is `|111⟩`. -/
noncomputable def ghz3 : EuclideanSpace ℂ (Fin 8) :=
  WithLp.toLp 2 (fun i => if i = 0 ∨ i = 7 then (1 : ℂ) / (Real.sqrt 2 : ℝ) else 0)

/-- The 3-qubit GHZ state is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have key : ∀ i : Fin 8, ‖ghz3.ofLp i‖ ^ 2 = if i = 0 ∨ i = 7 then (1 : ℝ) / 2 else 0 := by
    intro i
    by_cases h : i = 0 ∨ i = 7
    · simp only [ghz3, WithLp.ofLp_toLp, h, if_pos]
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hpos, div_pow, one_pow, h2]
    · simp [ghz3, h]
  rw [EuclideanSpace.norm_eq]
  simp only [key]
  rw [Fin.sum_univ_eight]
  norm_num [Fin.ext_iff]

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

