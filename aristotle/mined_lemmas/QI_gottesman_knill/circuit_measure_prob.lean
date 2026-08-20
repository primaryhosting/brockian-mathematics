/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

theorem circuit_measure_prob {n : ℕ} (C : List (Gate n)) (k : Fin n) :
    ((∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0),
        ‖circuitMat C x 0‖ ^ 2 : ℝ) : ℂ)
      = (1 + readout (simulate C (Pauli.mk 0 0 (unitVec k)))) / 2 := by
  have hconj : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [show star z = (starRingEnd ℂ) z from rfl, mul_comm, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  set M := circuitMat C with hMdef
  set c : Bits n → ℂ := fun x => ((‖M x 0‖ ^ 2 : ℝ) : ℂ) with hcdef
  have hZ : (Pauli.mk 0 0 (unitVec k) : Pauli n).toMat
      = Matrix.diagonal (fun x : Bits n => sgnC (x k)) := by
    ext y x
    by_cases h : y = x
    · subst h; simp [Pauli.toMat, iPowC_zero, dotB_unit_left]
    · simp [Pauli.toMat, h]
  have htot : ∑ x : Bits n, c x = 1 := by
    have h0 : ((M)ᴴ * M) 0 0 = 1 := by rw [circuitMat_conjTranspose_mul_self C]; simp
    rw [Matrix.mul_apply] at h0
    rw [← h0]
    exact Finset.sum_congr rfl (fun x _ => (hconj (M x 0)).symm)
  have hsig : ∑ x : Bits n, sgnC (x k) * c x
      = readout (simulate C (Pauli.mk 0 0 (unitVec k))) := by
    have h1 : (Mᴴ * (Pauli.mk 0 0 (unitVec k) : Pauli n).toMat * M) 0 0
        = readout (simulate C (Pauli.mk 0 0 (unitVec k))) := circuit_expectation _ _
    rw [← h1, hZ, Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply]
    show sgnC (x k) * ((‖M x 0‖ ^ 2 : ℝ) : ℂ) = _
    rw [← hconj (M x 0)]
    ring
  have e1 : ∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), sgnC (x k) * c x
      = ∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), c x := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Finset.mem_filter] at hx
    rw [hx.2, sgnC_zero, one_mul]
  have e2 : ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), sgnC (x k) * c x
      = -∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), c x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Finset.mem_filter] at hx
    rw [sgnC, if_neg hx.2]
    ring
  have hsplit : ∑ x : Bits n, c x
      = (∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), c x)
        + ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), c x :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsplit2 : ∑ x : Bits n, sgnC (x k) * c x
      = (∑ x ∈ Finset.univ.filter (fun x : Bits n => x k = 0), c x)
        - ∑ x ∈ Finset.univ.filter (fun x : Bits n => ¬ (x k = 0)), c x := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Bits n => x k = 0)
      (fun x => sgnC (x k) * c x), e1, e2]
    ring
  rw [Complex.ofReal_sum]
  rw [hsplit] at htot
  rw [hsplit2] at hsig
  linear_combination (1/2 : ℂ) * htot + (1/2 : ℂ) * hsig

/-! ## The gate matrices are the standard ones

These lemmas confirm that `gateMat` really is the usual Hadamard, phase and CNOT matrix in the
computational basis, so that the statements above are about genuine quantum circuits. -/

/-- The phase gate is `diag (1, i)` on qubit `i`. -/
