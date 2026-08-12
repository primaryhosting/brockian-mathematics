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

namespace QC

/-- The computational-basis ket `|v⟩` for a 4-qubit bit string `v : Fin 4 → Fin 2`. -/
noncomputable def ket (v : Fin 4 → Fin 2) : EuclideanSpace ℂ (Fin 4 → Fin 2) :=
  EuclideanSpace.single v 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩) / √2`. -/
noncomputable def ghz4 : EuclideanSpace ℂ (Fin 4 → Fin 2) :=
  ((Real.sqrt 2)⁻¹ : ℝ) • (ket (fun _ => 0) + ket (fun _ => 1))

/-- Coordinates of the GHZ state: `1/√2` on the all-zeros and all-ones strings, `0` elsewhere. -/
theorem ghz4_apply (v : Fin 4 → Fin 2) :
    ghz4 v = if (∀ i, v i = 0) ∨ (∀ i, v i = 1) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0 := by
  have h0 : (v = fun _ => (0 : Fin 2)) ↔ (∀ i, v i = 0) := funext_iff
  have h1 : (v = fun _ => (1 : Fin 2)) ↔ (∀ i, v i = 1) := funext_iff
  simp only [ghz4, ket, PiLp.smul_apply, PiLp.add_apply, EuclideanSpace.single_apply, h0, h1]
  by_cases a : (∀ i, v i = 0) <;> by_cases b : (∀ i, v i = 1) <;> simp [a, b]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have key : ∀ v : (Fin 4 → Fin 2), ‖ghz4 v‖ ^ 2 =
      if ((∀ i, v i = 0) ∨ (∀ i, v i = 1)) then (1/2 : ℝ) else 0 := by
    intro v
    rw [ghz4_apply v]
    split
    · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hs]
    · simp
  rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero]
  have hcard : (Finset.univ.filter (fun v : (Fin 4 → Fin 2) =>
      (∀ i, v i = 0) ∨ (∀ i, v i = 1))).card = 2 := by decide
  rw [hcard]
  norm_num

end QC

