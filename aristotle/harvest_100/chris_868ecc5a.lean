import Mathlib

/-!
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 7-qubit register is indexed by bit strings
`Fin 7 → Bool`; the state space is the complex Hilbert space
`EuclideanSpace ℂ (Fin 7 → Bool)`.

`ghz7` is the 7-qubit GHZ state `(|0000000⟩ + |1111111⟩)/√2`, written as
`(√2)⁻¹ • (e_{all-false} + e_{all-true})` where `e_b = EuclideanSpace.single b 1`
is the computational basis vector `|b⟩`. -/
noncomputable def ghz7 : EuclideanSpace ℂ (Fin 7 → Bool) :=
  (Real.sqrt 2)⁻¹ •
    (EuclideanSpace.single (fun _ => false) 1 + EuclideanSpace.single (fun _ => true) 1)

private lemma allFalse_ne_allTrue : ((fun _ => false) : Fin 7 → Bool) ≠ (fun _ => true) := by
  intro h
  have := congrFun h 0
  simp at this

/-- The un-normalized GHZ vector `|0000000⟩ + |1111111⟩` has norm `√2`. -/
private lemma norm_ghz7_unnormalized :
    ‖(EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ) :
        EuclideanSpace ℂ (Fin 7 → Bool))‖ = Real.sqrt 2 := by
  have hz := allFalse_ne_allTrue
  rw [EuclideanSpace.norm_eq]
  congr 1
  have key : ∀ b : (Fin 7 → Bool),
      ‖((EuclideanSpace.single (fun _ => false) (1 : ℂ)
          + EuclideanSpace.single (fun _ => true) (1 : ℂ) :
          EuclideanSpace ℂ (Fin 7 → Bool))).ofLp b‖ ^ 2
        = (if b = (fun _ => false) then (1 : ℝ) else 0)
          + (if b = (fun _ => true) then (1 : ℝ) else 0) := by
    intro b
    by_cases h1 : b = (fun _ => false)
    · subst h1; simp [EuclideanSpace.single_apply, hz]
    · by_cases h2 : b = (fun _ => true)
      · subst h2; simp [EuclideanSpace.single_apply, Ne.symm hz]
      · simp [EuclideanSpace.single_apply, h1, h2]
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  norm_num

/-- **The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector.** -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [ghz7, norm_smul, norm_ghz7_unnormalized, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (inv_pos.mpr h2)), inv_mul_cancel₀ (ne_of_gt h2)]

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

