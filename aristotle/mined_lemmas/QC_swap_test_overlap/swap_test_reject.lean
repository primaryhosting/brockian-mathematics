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

open scoped ComplexConjugate

namespace QC

variable {n : ℕ}

/-- The product state `ψ ⊗ φ` of two `n`-level registers, as a vector indexed by
pairs of basis labels. -/

theorem swap_test_reject (ψ φ : EuclideanSpace ℂ (Fin n))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    rejectProb ψ φ = (1 - ‖(inner ℂ ψ φ : ℂ)‖ ^ 2) / 2 := by
  set S : ℂ := (inner ℂ ψ φ : ℂ) with hSdef
  have key : ((rejectProb ψ φ : ℝ) : ℂ) = ((( 1 - ‖S‖ ^ 2) / 2 : ℝ) : ℂ) := by
    rw [rejectProb, ofReal_sum_norm_sq]
    have hterm : ∀ x : Fin n × Fin n,
        swapTestFinal ψ φ (1, x) * conj (swapTestFinal ψ φ (1, x))
          = ((ψ x.1 * φ x.2 + (-1) * (φ x.1 * ψ x.2))
              * conj (ψ x.1 * φ x.2 + (-1) * (φ x.1 * ψ x.2))) / 4 := by
      intro x
      rw [swapTestFinal_one]
      simp only [map_div₀, Complex.conj_ofNat]
      ring
    rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_div,
      sum_branch_sq ψ φ hψ hφ (-1), ← hSdef, Complex.mul_conj' S]
    simp only [map_neg, map_one]
    push_cast
    ring
  have hre := congrArg Complex.re key
  rwa [Complex.ofReal_re, Complex.ofReal_re] at hre

/-- Sanity check: the two outcome probabilities sum to one. -/
