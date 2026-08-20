import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational basis states of 6 qubits, indexed by bit strings `Fin 6 → Bool`. -/
abbrev Qubits6 := Fin 6 → Bool

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
Hilbert space `EuclideanSpace ℂ (Fin 6 → Bool)`. -/
noncomputable def ghz6 : EuclideanSpace ℂ Qubits6 :=
  WithLp.toLp 2 fun b =>
    if b = (fun _ => false) ∨ b = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The all-zeros and all-ones bit strings are distinct. -/
lemma allFalse_ne_allTrue : (fun _ => false : Qubits6) ≠ (fun _ => true) := by
  intro h
  simpa using congrFun h 0

/-- `ghz6` really is the superposition `(|000000⟩ + |111111⟩)/√2` of the two
computational basis vectors. -/
theorem ghz6_eq_superposition :
    ghz6 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hne := allFalse_ne_allTrue
  ext b
  by_cases h1 : b = (fun _ => false)
  · simp [ghz6, h1, EuclideanSpace.single_apply, hne]
  · by_cases h2 : b = (fun _ => true)
    · simp [ghz6, h2, EuclideanSpace.single_apply, hne.symm]
    · simp [ghz6, h1, h2, EuclideanSpace.single_apply]

/-- The 6-qubit GHZ state is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : ∑ b : Qubits6, ‖ghz6.ofLp b‖ ^ 2 = 1 := by
    have hcongr : ∀ b : Qubits6, ‖ghz6.ofLp b‖ ^ 2
        = (1 / 2 : ℝ) * (if b = (fun _ => false) ∨ b = (fun _ => true) then (1:ℝ) else 0) := by
      intro b
      by_cases h : b = (fun _ => false) ∨ b = (fun _ => true)
      · have : ghz6.ofLp b = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ghz6, h]
        have hnorm : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ = 1 / Real.sqrt 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        rw [this, hnorm, if_pos h, div_pow, hsq]
        norm_num
      · have : ghz6.ofLp b = 0 := by simp [ghz6, h]
        simp [this, h]
    rw [Finset.sum_congr rfl (fun b _ => hcongr b), ← Finset.mul_sum, Finset.sum_boole]
    have hcard : (Finset.univ.filter
        (fun b : Qubits6 => b = (fun _ => false) ∨ b = (fun _ => true))).card = 2 := by
      decide
    rw [hcard]
    norm_num
  rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]

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

