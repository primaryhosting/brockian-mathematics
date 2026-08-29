/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 8 → Bool)`, whose index type `Fin 8 → Bool` enumerates the
`2^8` computational basis states. -/
noncomputable def ghz8 : EuclideanSpace ℂ (Fin 8 → Bool) :=
  WithLp.toLp 2 (fun v =>
    if v = (fun _ => false) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if v = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0)

/-- `ghz8` really is `(|0…0⟩ + |1…1⟩)/√2`: it is `1/√2` times the sum of the two
computational basis vectors indexed by the all-zeros and all-ones bit strings. -/
theorem ghz8_eq_smul_add_single :
    ghz8 = (((1 / Real.sqrt 2 : ℝ) : ℂ)) •
      (EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hab : (fun _ => false : Fin 8 → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    simp at this
  ext v
  by_cases h1 : v = (fun _ => false)
  · subst h1; simp [ghz8, EuclideanSpace.single_apply, hab]
  · by_cases h2 : v = (fun _ => true) <;>
      simp [ghz8, EuclideanSpace.single_apply, h1, h2, Ne.symm hab]

/-- The 8-qubit GHZ state is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  have hab : (fun _ => false : Fin 8 → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    simp at this
  rw [EuclideanSpace.norm_eq]
  simp only [ghz8, WithLp.ofLp_toLp]
  have key : ∀ v : Fin 8 → Bool,
      ‖(if v = (fun _ => false) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
        else if v = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)‖ ^ 2
      = (if v = (fun _ => false) then (1 / 2 : ℝ) else 0)
        + (if v = (fun _ => true) then (1 / 2 : ℝ) else 0) := by
    intro v
    by_cases h1 : v = (fun _ => false)
    · subst h1; simp [hab, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
        Real.sq_sqrt]
    · by_cases h2 : v = (fun _ => true) <;>
        simp [h1, h2, Ne.symm hab, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg 2), Real.sq_sqrt]
  rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_add_distrib]
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

