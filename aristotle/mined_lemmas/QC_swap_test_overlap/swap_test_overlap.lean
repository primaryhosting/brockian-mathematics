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
