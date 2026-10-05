import Mathlib

/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 5 → Bool)` whose coordinates are indexed by the computational
basis states (bit strings of length 5). -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Bool) :=
  WithLp.toLp 2 (fun v =>
    if v = (fun _ => false) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if v = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0)

/-- `ghz5` is indeed `(1/√2) • (|00000⟩ + |11111⟩)`, written with the standard
basis vectors `EuclideanSpace.single`. -/
theorem ghz5_eq_smul_add_single :
    ghz5 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hne : ¬ ((fun _ => false : Fin 5 → Bool) = (fun _ => true)) := by
    intro hc; have := congrFun hc 0; simp at this
  ext v
  by_cases h1 : v = (fun _ => false)
  · simp [ghz5, h1, hne, EuclideanSpace.single_apply]
  · by_cases h3 : v = (fun _ => true)
    · simp [ghz5, h3, Ne.symm hne, EuclideanSpace.single_apply]
    · simp [ghz5, h1, h3, EuclideanSpace.single_apply]

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2` is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : ∀ v : Fin 5 → Bool, ‖ghz5.ofLp v‖ ^ 2
      = (if v = (fun _ => false) then (1:ℝ)/2 else 0)
        + (if v = (fun _ => true) then (1:ℝ)/2 else 0) := by
    intro v
    by_cases h1 : v = (fun _ => false)
    · have h2' : ¬ (v = (fun _ => true)) := by
        rw [h1]; intro hc; have := congrFun hc 0; simp at this
      rw [h1] at h2' ⊢
      simp [ghz5, h2', hsq, abs_of_pos h2]
    · by_cases h3 : v = (fun _ => true)
      · have h1' : ¬ ((fun _ => true : Fin 5 → Bool) = (fun _ => false)) := by
          intro hc; have := congrFun hc 0; simp at this
        rw [h3] at h1 ⊢
        simp [ghz5, h1', hsq, abs_of_pos h2]
      · simp [ghz5, h1, h3]
  rw [EuclideanSpace.norm_eq]
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
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

