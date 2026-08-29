/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 8 qubits: the Hilbert space `ℂ^(2^8)`, indexed by the
computational basis states `Fin 8 → Bool`. -/
abbrev Qubits8 : Type := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The all-zeros computational basis state `|0…0⟩`. -/
noncomputable def ket0 : Qubits8 := EuclideanSpace.single (fun _ => false) 1

/-- The all-ones computational basis state `|1…1⟩`. -/
noncomputable def ket1 : Qubits8 := EuclideanSpace.single (fun _ => true) 1

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
noncomputable def ghz8 : Qubits8 := ((1 / Real.sqrt 2 : ℝ) : ℂ) • (ket0 + ket1)

/-- Coordinates of the GHZ state: it is `1/√2` on the all-zeros and all-ones basis
states and `0` elsewhere. -/
lemma ghz8_apply (x : Fin 8 → Bool) :
    ghz8 x = if (x = fun _ => false) ∨ (x = fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else 0 := by
  have hne : (fun _ => false : Fin 8 → Bool) ≠ (fun _ => true) := by decide
  simp only [ghz8, ket0, ket1, PiLp.smul_apply, PiLp.add_apply, EuclideanSpace.single_apply,
    smul_eq_mul]
  by_cases h0 : x = fun _ => false
  · subst h0
    simp [hne]
  · by_cases h1 : x = fun _ => true
    · subst h1
      simp [Ne.symm hne]
    · simp [h0, h1]

/-- **The 8-qubit GHZ state is a unit vector.** -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ x : Fin 8 → Bool,
      ‖ghz8 x‖ ^ 2 = if (x = fun _ => false) ∨ (x = fun _ => true) then (1 / 2 : ℝ) else 0 := by
    intro x
    rw [ghz8_apply]
    split
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    · simp
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  have hc : (Finset.univ.filter
      (fun x : Fin 8 → Bool => (x = fun _ => false) ∨ (x = fun _ => true))).card = 2 := by
    decide
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

