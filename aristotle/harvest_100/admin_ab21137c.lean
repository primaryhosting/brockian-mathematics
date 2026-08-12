/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 4 qubits: the 16-dimensional complex Hilbert space whose
computational basis is indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 : Type := EuclideanSpace ℂ (Fin 4 → Fin 2)

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`. -/
noncomputable def ghz4 : Qubits4 :=
  (1 / Real.sqrt 2 : ℝ) •
    (EuclideanSpace.single (fun _ => 0) 1 + EuclideanSpace.single (fun _ => 1) 1)

/-- The amplitudes of `ghz4`: `1/√2` on `|0000⟩` and `|1111⟩`, and `0` elsewhere. -/
theorem ghz4_apply (x : Fin 4 → Fin 2) :
    ghz4.ofLp x =
      if x = (fun _ => 0) ∨ x = (fun _ => 1) then (1 / Real.sqrt 2 : ℝ) else 0 := by
  have hne : (fun _ => (0 : Fin 2)) ≠ (fun _ : Fin 4 => (1 : Fin 2)) := by
    intro h; have := congrFun h 0; simp at this
  by_cases h0 : x = (fun _ => 0)
  · subst h0; simp [ghz4, EuclideanSpace.single_apply, hne]
  · by_cases h1 : x = (fun _ => 1)
    · subst h1; simp [ghz4, EuclideanSpace.single_apply, Ne.symm hne]
    · simp [ghz4, EuclideanSpace.single_apply, h0, h1]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  have hne : (fun _ => (0 : Fin 2)) ≠ (fun _ : Fin 4 => (1 : Fin 2)) := by
    intro h; have := congrFun h 0; simp at this
  -- the two computational basis vectors involved are orthogonal
  have hinner : inner ℂ (EuclideanSpace.single (𝕜 := ℂ) (fun _ => (0 : Fin 2)) 1)
      (EuclideanSpace.single (𝕜 := ℂ) (fun _ : Fin 4 => (1 : Fin 2)) (1 : ℂ)) = 0 := by
    simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hne]
  -- Pythagoras (`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`) plus
  -- `EuclideanSpace.norm_single`
  have hsum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner
  rw [EuclideanSpace.norm_single, EuclideanSpace.norm_single] at hsum
  simp only [norm_one, one_mul] at hsum
  have h2 : ‖(EuclideanSpace.single (𝕜 := ℂ) (fun _ => (0 : Fin 2)) 1 +
      EuclideanSpace.single (𝕜 := ℂ) (fun _ : Fin 4 => (1 : Fin 2)) 1)‖ = Real.sqrt 2 := by
    have hnn := norm_nonneg (EuclideanSpace.single (𝕜 := ℂ) (fun _ => (0 : Fin 2)) 1 +
      EuclideanSpace.single (𝕜 := ℂ) (fun _ : Fin 4 => (1 : Fin 2)) 1)
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hsum]
  rw [ghz4, norm_smul, h2, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2)]
  field_simp

end QC

#print axioms QC.ghz4_normalized
#print axioms QC.ghz4_apply

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

