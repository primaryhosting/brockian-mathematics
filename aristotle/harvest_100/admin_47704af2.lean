/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 6-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 6 → Bool)` whose computational-basis index set is the set of
bitstrings of length `6`. -/
noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Bool) :=
  WithLp.toLp 2 (fun b : (Fin 6 → Bool) =>
    if (∀ i, b i = false) ∨ (∀ i, b i = true) then ((Real.sqrt 2)⁻¹ : ℂ) else 0)

/-- `ghz6` really is `(|0…0⟩ + |1…1⟩)/√2`: it is `(√2)⁻¹` times the sum of the two
computational basis vectors indexed by the all-zeros and all-ones bitstrings. -/
theorem ghz6_eq_smul_add_single :
    ghz6 = ((Real.sqrt 2)⁻¹ : ℂ) •
      (EuclideanSpace.single (fun _ : Fin 6 => false) (1 : ℂ) +
       EuclideanSpace.single (fun _ : Fin 6 => true) (1 : ℂ)) := by
  ext b
  by_cases h0 : b = (fun _ : Fin 6 => false)
  · subst h0
    have hne : ¬ ((fun _ : Fin 6 => false) = fun _ => true) := by decide
    simp [ghz6, EuclideanSpace.single_apply, hne]
  · by_cases h1 : b = (fun _ : Fin 6 => true)
    · subst h1
      have hne : ¬ ((fun _ : Fin 6 => true) = fun _ => false) := by decide
      simp [ghz6, EuclideanSpace.single_apply, hne]
    · have hf : ¬ (∀ i, b i = false) := fun h => h0 (funext h)
      have ht : ¬ (∀ i, b i = true) := fun h => h1 (funext h)
      simp [ghz6, EuclideanSpace.single_apply, hf, ht, h0, h1]

/-- The 6-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ b : (Fin 6 → Bool), ‖ghz6.ofLp b‖ ^ 2 =
      if ((∀ i, b i = false) ∨ (∀ i, b i = true)) then (2 : ℝ)⁻¹ else 0 := by
    intro b
    by_cases hb : ((∀ i, b i = false) ∨ (∀ i, b i = true)) <;>
      simp [ghz6, hb, Real.sq_sqrt]
  simp only [h, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter
      (fun b : Fin 6 → Bool => (∀ i, b i = false) ∨ (∀ i, b i = true))).card = 2 := by decide
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

