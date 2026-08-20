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

lemma sum_mul_conj_of_norm_one (ψ : EuclideanSpace ℂ (Fin n)) (h : ‖ψ‖ = 1) :
    ∑ i, ψ i * conj (ψ i) = 1 := by
  have h2 : ∑ i, ‖ψ i‖ ^ 2 = 1 := by
    have hn := EuclideanSpace.norm_eq ψ
    rw [h, eq_comm, Real.sqrt_eq_one] at hn
    exact hn
  have h3 : ∑ i, ψ i * conj (ψ i) = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj']
    push_cast; ring
  rw [h3, ← Complex.ofReal_sum, h2, Complex.ofReal_one]

/-- The overlap `⟨ψ|φ⟩` written as an explicit sum. -/
