/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The all-zeros computational basis label `|0000⟩` for four qubits. -/
def allZeros : Fin 4 → Fin 2 := fun _ => 0

/-- The all-ones computational basis label `|1111⟩` for four qubits. -/
def allOnes : Fin 4 → Fin 2 := fun _ => 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(Fin 4 → Fin 2)` of four qubits. -/
noncomputable def ghz4 : EuclideanSpace ℂ (Fin 4 → Fin 2) :=
  WithLp.toLp 2 (fun x => if x = allZeros then ((Real.sqrt 2)⁻¹ : ℝ)
           else if x = allOnes then ((Real.sqrt 2)⁻¹ : ℝ) else 0)

lemma allZeros_ne_allOnes : (allZeros : Fin 4 → Fin 2) ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

lemma ghz4_apply_allZeros : ghz4.ofLp allZeros = ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [ghz4]

lemma ghz4_apply_allOnes : ghz4.ofLp allOnes = ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [ghz4, (allZeros_ne_allOnes).symm]

lemma ghz4_apply_other {x : Fin 4 → Fin 2} (h0 : x ≠ allZeros) (h1 : x ≠ allOnes) :
    ghz4.ofLp x = 0 := by
  simp [ghz4, h0, h1]

lemma norm_sq_coeff : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- `ghz4` really is `(|0000⟩ + |1111⟩)/√2`, written in terms of the computational
basis vectors `EuclideanSpace.single`. -/
lemma ghz4_eq_smul_add_single :
    ghz4 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      (EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ)) := by
  ext x
  by_cases h0 : x = allZeros
  · subst h0
    simp [ghz4, EuclideanSpace.single_apply, allZeros_ne_allOnes]
  · by_cases h1 : x = allOnes
    · subst h1
      simp [ghz4, EuclideanSpace.single_apply, h0]
    · simp [ghz4, EuclideanSpace.single_apply, h0, h1]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ x : Fin 4 → Fin 2, ‖ghz4.ofLp x‖ ^ 2)
      = ‖ghz4.ofLp allZeros‖ ^ 2 + ‖ghz4.ofLp allOnes‖ ^ 2 := by
    refine Finset.sum_eq_add_of_mem _ _ (Finset.mem_univ _) (Finset.mem_univ _)
      allZeros_ne_allOnes ?_
    intro c _ hc
    rw [ghz4_apply_other hc.1 hc.2]
    simp
  rw [hsum, ghz4_apply_allZeros, ghz4_apply_allOnes, norm_sq_coeff]
  norm_num

end QC

#print axioms QC.ghz4_normalized

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

