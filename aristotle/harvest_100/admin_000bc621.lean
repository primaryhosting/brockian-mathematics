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

/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Finset Complex

variable {n : ℕ}

/-- The inner product `⟨ψ|φ⟩` of two (finite dimensional) state vectors,
antilinear in the first argument. -/
noncomputable def braket (ψ φ : Fin n → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (ψ i) * φ i

/-- The input state of the swap test: the ancilla qubit in `|0⟩` and the two
registers holding `ψ` and `φ`.  A vector of the composite system is described by
its amplitudes, indexed by (ancilla bit, first register, second register). -/
def inputState (ψ φ : Fin n → ℂ) : Fin 2 × Fin n × Fin n → ℂ :=
  fun p => if p.1 = 0 then ψ p.2.1 * φ p.2.2 else 0

/-- A Hadamard gate acting on the ancilla qubit. -/
noncomputable def hadamardAncilla (v : Fin 2 × Fin n × Fin n → ℂ) :
    Fin 2 × Fin n × Fin n → ℂ :=
  fun p => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
    (v (0, p.2) + (if p.1 = 0 then 1 else -1) * v (1, p.2))

/-- The controlled swap (Fredkin) gate: the two registers are exchanged when the
ancilla qubit is `|1⟩`. -/
def cswap (v : Fin 2 × Fin n × Fin n → ℂ) : Fin 2 × Fin n × Fin n → ℂ :=
  fun p => if p.1 = 0 then v (0, p.2.1, p.2.2) else v (1, p.2.2, p.2.1)

/-- The state at the end of the swap test circuit:
Hadamard on the ancilla, controlled swap, Hadamard on the ancilla. -/
noncomputable def swapTestFinal (ψ φ : Fin n → ℂ) : Fin 2 × Fin n × Fin n → ℂ :=
  hadamardAncilla (cswap (hadamardAncilla (inputState ψ φ)))

/-- The probability that the swap test accepts, i.e. that measuring the ancilla
qubit of the final state returns `0`. -/
noncomputable def acceptProb (ψ φ : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖swapTestFinal ψ φ (0, i, j)‖ ^ 2

lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq z).symm

lemma sqrt_two_inv_sq : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  field_simp
  linear_combination -h

/-- The accepted branch of the final state carries the symmetrised amplitudes. -/
lemma swapTestFinal_zero (ψ φ : Fin n → ℂ) (i j : Fin n) :
    swapTestFinal ψ φ (0, i, j) = (1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i) := by
  simp only [swapTestFinal, hadamardAncilla, cswap, inputState]
  norm_num
  ring_nf
  rw [show (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 by rw [sq]; exact sqrt_two_inv_sq]
  ring

/-- **Swap test.**  For two normalised states `ψ` and `φ`, the swap test accepts
with probability `(1 + |⟨ψ|φ⟩|²)/2`. -/
theorem swap_test_overlap (ψ φ : Fin n → ℂ)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) :
    acceptProb ψ φ = (1 + ‖braket ψ φ‖ ^ 2) / 2 := by
  have hψ' : ∑ i, ψ i * (starRingEnd ℂ) (ψ i) = 1 := by
    have h : ∑ i, ψ i * (starRingEnd ℂ) (ψ i) = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => (ofReal_norm_sq _).symm
    rw [h, hψ, Complex.ofReal_one]
  have hφ' : ∑ i, φ i * (starRingEnd ℂ) (φ i) = 1 := by
    have h : ∑ i, φ i * (starRingEnd ℂ) (φ i) = ((∑ i, ‖φ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => (ofReal_norm_sq _).symm
    rw [h, hφ, Complex.ofReal_one]
  have hA : (∑ i, ψ i * (starRingEnd ℂ) (φ i)) = (starRingEnd ℂ) (braket ψ φ) := by
    simp [braket, map_sum, mul_comm]
  have hB : (∑ j, φ j * (starRingEnd ℂ) (ψ j)) = braket ψ φ := by
    simp [braket, mul_comm]
  have h1 : ((acceptProb ψ φ : ℝ) : ℂ)
      = ∑ i, ∑ j, ((1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i)) *
          (starRingEnd ℂ) ((1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i)) := by
    rw [acceptProb, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ofReal_norm_sq, swapTestFinal_zero]
  have h2 : (∑ i, ∑ j, ((1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i)) *
        (starRingEnd ℂ) ((1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i)))
      = (1 / 4 : ℂ) * ((∑ i, ψ i * (starRingEnd ℂ) (ψ i)) *
            (∑ j, φ j * (starRingEnd ℂ) (φ j))
          + (∑ i, ψ i * (starRingEnd ℂ) (φ i)) * (∑ j, φ j * (starRingEnd ℂ) (ψ j))
          + (∑ i, φ i * (starRingEnd ℂ) (ψ i)) * (∑ j, ψ j * (starRingEnd ℂ) (φ j))
          + (∑ i, φ i * (starRingEnd ℂ) (φ i)) * (∑ j, ψ j * (starRingEnd ℂ) (ψ j))) := by
    have hpt : ∀ i j : Fin n, ((1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i)) *
        (starRingEnd ℂ) ((1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i))
        = (1 / 4 : ℂ) * ((ψ i * (starRingEnd ℂ) (ψ i)) * (φ j * (starRingEnd ℂ) (φ j))
            + (ψ i * (starRingEnd ℂ) (φ i)) * (φ j * (starRingEnd ℂ) (ψ j))
            + (φ i * (starRingEnd ℂ) (ψ i)) * (ψ j * (starRingEnd ℂ) (φ j))
            + (φ i * (starRingEnd ℂ) (φ i)) * (ψ j * (starRingEnd ℂ) (ψ j))) := by
      intro i j
      simp only [map_mul, map_add, map_div₀, map_one, map_ofNat]
      ring
    simp only [hpt, ← Finset.mul_sum]
    congr 1
    simp [Finset.sum_add_distrib, Finset.sum_mul_sum]
  have h3 : ((acceptProb ψ φ : ℝ) : ℂ) = (((1 + ‖braket ψ φ‖ ^ 2) / 2 : ℝ) : ℂ) := by
    rw [h1, h2, hψ', hφ', hA, hB, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
      ofReal_norm_sq, Complex.ofReal_ofNat]
    ring
  exact_mod_cast h3

/-- Sanity check: on two copies of the same normalised state the swap test always
accepts. -/
theorem swap_test_same (ψ : Fin n → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    acceptProb ψ ψ = 1 := by
  have hb : braket ψ ψ = 1 := by
    have h : braket ψ ψ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [braket, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ofReal_norm_sq, mul_comm]
    rw [h, hψ, Complex.ofReal_one]
  rw [swap_test_overlap ψ ψ hψ hψ, hb]
  norm_num

/-- Sanity check: on orthogonal states the swap test accepts with probability `1/2`. -/
theorem swap_test_orthogonal (ψ φ : Fin n → ℂ)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) (h : braket ψ φ = 0) :
    acceptProb ψ φ = 1 / 2 := by
  rw [swap_test_overlap ψ φ hψ hφ, h]
  norm_num

end QC

