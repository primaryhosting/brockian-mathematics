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

(The header block is repeated above as a plain comment because Lean requires
`import` commands to precede any module docstring.)
-/

namespace QC

/-- Computational basis labels for five qubits: bitstrings of length `5`. -/
abbrev Q5 := Fin 5 → Bool

/-- The all-zeros bitstring, labelling `|00000⟩`. -/
def allZero : Q5 := fun _ => false

/-- The all-ones bitstring, labelling `|11111⟩`. -/
def allOne : Q5 := fun _ => true

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector of the
Hilbert space `ℂ^(2^5)` indexed by length-5 bitstrings. -/
noncomputable def ghz5 : EuclideanSpace ℂ Q5 :=
  WithLp.toLp 2 (fun x => if x = allZero ∨ x = allOne then ((Real.sqrt 2)⁻¹ : ℝ) else 0)

theorem allZero_ne_allOne : (allZero : Q5) ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- The 5-qubit GHZ state is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  have hc : ‖((((Real.sqrt 2)⁻¹ : ℝ) : ℂ))‖ ^ 2 = (2 : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_pow, Real.sq_sqrt (by norm_num)]
  have key : ∀ x : Q5, ‖ghz5.ofLp x‖ ^ 2
      = (if x = allZero then (2 : ℝ)⁻¹ else 0)
        + (if x = allOne then (2 : ℝ)⁻¹ else 0) := by
    intro x
    by_cases h0 : x = allZero
    · have h1 : x ≠ allOne := by
        rw [h0]; exact allZero_ne_allOne
      simp only [ghz5, WithLp.ofLp_toLp, h0, true_or, if_true]
      rw [if_neg allZero_ne_allOne, add_zero]
      exact hc
    · by_cases h1 : x = allOne
      · simp only [ghz5, WithLp.ofLp_toLp, h1, or_true, if_true]
        rw [if_neg allZero_ne_allOne.symm, zero_add]
        exact hc
      · simp [ghz5, h0, h1]
  rw [EuclideanSpace.norm_eq]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]
  rw [show (2:ℝ)⁻¹ + (2:ℝ)⁻¹ = 1 by norm_num, Real.sqrt_one]

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

