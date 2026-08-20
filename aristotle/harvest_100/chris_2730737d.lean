/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
`EuclideanSpace ℂ (Fin 5 → Fin 2)` of amplitudes indexed by 5-bit strings. -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Fin 2) :=
  WithLp.toLp 2 (fun b => if (∀ i, b i = 0) ∨ (∀ i, b i = 1) then ((1 : ℂ) / (Real.sqrt 2 : ℝ)) else 0)

/-- `ghz5` really is `(|00000⟩ + |11111⟩)/√2`, expressed in the standard basis. -/
theorem ghz5_eq_smul_add_single : ghz5 = ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) •
    (EuclideanSpace.single (fun _ => (0 : Fin 2)) (1 : ℂ)
      + EuclideanSpace.single (fun _ => (1 : Fin 2)) (1 : ℂ)) := by
  ext b
  by_cases hp : ∀ i, b i = 0 <;> by_cases hq : ∀ i, b i = 1 <;>
    simp [ghz5, EuclideanSpace.single_apply, funext_iff, eq_comm, one_div, hp, hq]

/-- The 5-qubit GHZ state is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have key : ∀ b : Fin 5 → Fin 2,
      ‖ghz5.ofLp b‖ ^ 2 = if (∀ i, b i = 0) ∨ (∀ i, b i = 1) then (1 / 2 : ℝ) else 0 := by
    intro b
    by_cases hb : (∀ i, b i = 0) ∨ (∀ i, b i = 1) <;> simp [ghz5, hb]
  simp only [key]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun b : Fin 5 → Fin 2 => (∀ i, b i = 0) ∨ (∀ i, b i = 1))).card = 2 := by decide
  rw [hcard]
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

