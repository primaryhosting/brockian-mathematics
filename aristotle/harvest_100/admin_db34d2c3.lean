/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis of a 6-qubit system is indexed by bit strings
`Fin 6 → Fin 2`; states live in the Hilbert space `EuclideanSpace ℂ (Fin 6 → Fin 2)`
(a 64-dimensional complex inner product space). -/
abbrev Qubits6 := EuclideanSpace ℂ (Fin 6 → Fin 2)

/-- The all-zeros bit string `000000`. -/
def allZeros : Fin 6 → Fin 2 := fun _ => 0

/-- The all-ones bit string `111111`. -/
def allOnes : Fin 6 → Fin 2 := fun _ => 1

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`. -/
noncomputable def ghz6 : Qubits6 :=
  ((1 : ℂ) / (Real.sqrt 2 : ℝ)) •
    (EuclideanSpace.single allZeros 1 + EuclideanSpace.single allOnes 1)

private lemma allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

private lemma norm_basis_sum :
    ‖(EuclideanSpace.single allZeros 1 + EuclideanSpace.single allOnes 1 : Qubits6)‖
      = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have key : ∀ i : Fin 6 → Fin 2,
      ‖(WithLp.ofLp (EuclideanSpace.single allZeros (1 : ℂ)
          + EuclideanSpace.single allOnes (1 : ℂ) : Qubits6)) i‖ ^ 2
        = (if i = allZeros then (1 : ℝ) else 0) + (if i = allOnes then (1 : ℝ) else 0) := by
    intro i
    by_cases h0 : i = allZeros <;> by_cases h1 : i = allOnes <;>
      simp [EuclideanSpace.single_apply, h0, h1, allZeros_ne_allOnes,
        Ne.symm allZeros_ne_allOnes]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  norm_num

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2` is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  rw [ghz6, norm_smul, norm_basis_sum]
  simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2]
  field_simp

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

