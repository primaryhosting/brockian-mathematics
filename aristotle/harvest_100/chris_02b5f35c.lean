import Mathlib

/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Finset

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 5 → Bool)` whose basis vectors `EuclideanSpace.single b 1` are the
computational basis states `|b⟩` indexed by bit strings `b : Fin 5 → Bool`. -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Bool) :=
  ((Real.sqrt 2)⁻¹ : ℂ) •
    (EuclideanSpace.single (fun _ => false) 1 + EuclideanSpace.single (fun _ => true) 1)

/-- The coordinates of the GHZ state: `1/√2` on the all-zeros and all-ones bit strings,
and `0` elsewhere. -/
lemma ghz5_apply (b : Fin 5 → Bool) :
    ghz5 b = if b = (fun _ => false) ∨ b = (fun _ => true) then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := by
  by_cases h1 : b = (fun _ => false)
  · subst h1
    simp only [ghz5, EuclideanSpace.single_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    norm_num
    decide
  · by_cases h2 : b = (fun _ => true)
    · subst h2
      simp only [ghz5, EuclideanSpace.single_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      norm_num
      decide
    · simp [ghz5, EuclideanSpace.single_apply, h1, h2]

/-- **The 5-qubit GHZ state is a unit vector.** -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ b : Fin 5 → Bool, ‖ghz5 b‖ ^ 2 =
      if b = (fun _ => false) ∨ b = (fun _ => true) then (1 / 2 : ℝ) else 0 := by
    intro b
    rw [ghz5_apply b]
    by_cases hb : b = (fun _ => false) ∨ b = (fun _ => true) <;>
      simp [hb, Real.sq_sqrt]
  simp_rw [h]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  have hc : (Finset.univ.filter (fun b : Fin 5 → Bool =>
      b = (fun _ => false) ∨ b = (fun _ => true))).card = 2 := by decide
  rw [hc]
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

