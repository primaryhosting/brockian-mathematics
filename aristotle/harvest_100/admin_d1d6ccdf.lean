/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis labels for 5 qubits: functions `Fin 5 → Bool`
(so the state space `EuclideanSpace ℂ (Fin 5 → Bool)` is the 32-dimensional
tensor product of five qubit spaces). -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros label `|00000⟩`. -/
def allZero : Qubits5 := fun _ => false

/-- The all-ones label `|11111⟩`. -/
def allOne : Qubits5 := fun _ => true

theorem allZero_ne_allOne : allZero ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`. -/
noncomputable def ghz5 : EuclideanSpace ℂ Qubits5 :=
  WithLp.toLp 2 (fun v => if v = allZero ∨ v = allOne then (1 / Real.sqrt 2 : ℝ) else 0)

/-- `ghz5` is indeed `(1/√2) • (|00000⟩ + |11111⟩)` in terms of the standard basis. -/
theorem ghz5_eq_smul_add_single :
    ghz5 = (1 / Real.sqrt 2 : ℝ) •
      (EuclideanSpace.single allZero (1 : ℂ) + EuclideanSpace.single allOne (1 : ℂ)) := by
  ext v
  by_cases h1 : v = allZero
  · subst h1
    simp [ghz5, EuclideanSpace.single_apply, Ne.symm allZero_ne_allOne]
  · by_cases h2 : v = allOne
    · subst h2
      simp [ghz5, EuclideanSpace.single_apply, allZero_ne_allOne]
    · simp [ghz5, EuclideanSpace.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]

/-- **The 5-qubit GHZ state is a unit vector.** -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  have key : ∀ v : Qubits5, ‖(ghz5.ofLp) v‖ ^ 2
      = (if v = allZero then (1 : ℝ) / 2 else 0)
        + (if v = allOne then (1 : ℝ) / 2 else 0) := by
    intro v
    rcases eq_or_ne v allZero with h1 | h1
    · subst h1
      simp [ghz5, allZero_ne_allOne, Complex.norm_real, Real.sq_sqrt]
    · rcases eq_or_ne v allOne with h2 | h2
      · subst h2
        simp [ghz5, Ne.symm allZero_ne_allOne, Complex.norm_real, Real.sq_sqrt]
      · simp [ghz5, h1, h2]
  rw [EuclideanSpace.norm_eq]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
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

