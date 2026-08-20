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

lemma sum_branch_sq (ψ φ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (c : ℂ) :
    ∑ x : Fin n × Fin n,
        (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2)) * conj (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2))
      = 1 + c * conj c
        + (c + conj c) * ((inner ℂ ψ φ : ℂ) * conj (inner ℂ ψ φ : ℂ)) := by
  have rank_one_double_sum : ∀ f1 g1 f2 g2 f3 g3 f4 g4 : Fin n → ℂ,
      ∑ i, ∑ j, (f1 i * g1 j + f2 i * g2 j + f3 i * g3 j + f4 i * g4 j)
        = (∑ i, f1 i) * (∑ j, g1 j) + (∑ i, f2 i) * (∑ j, g2 j)
          + (∑ i, f3 i) * (∑ j, g3 j) + (∑ i, f4 i) * (∑ j, g4 j) := by
    intro f1 g1 f2 g2 f3 g3 f4 g4
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hA : ∑ i, ψ i * conj (ψ i) = 1 := sum_mul_conj_of_norm_one ψ hψ
  have hB : ∑ i, φ i * conj (φ i) = 1 := sum_mul_conj_of_norm_one φ hφ
  set S : ℂ := (inner ℂ ψ φ : ℂ) with hSdef
  have hS : S = ∑ i, φ i * conj (ψ i) := by
    rw [hSdef, inner_eq_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hSc : conj S = ∑ i, ψ i * conj (φ i) := by
    rw [hSdef, inner_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  have hterm : ∀ x : Fin n × Fin n,
      (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2)) * conj (ψ x.1 * φ x.2 + c * (φ x.1 * ψ x.2))
        = (ψ x.1 * conj (ψ x.1)) * (φ x.2 * conj (φ x.2))
          + (ψ x.1 * conj (φ x.1)) * (conj c * (φ x.2 * conj (ψ x.2)))
          + (φ x.1 * conj (ψ x.1)) * (c * (ψ x.2 * conj (φ x.2)))
          + (φ x.1 * conj (φ x.1)) * ((c * conj c) * (ψ x.2 * conj (ψ x.2))) := by
    intro x
    simp only [map_add, map_mul]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Fintype.sum_prod_type]
  dsimp only
  rw [rank_one_double_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    hA, hB, ← hS, ← hSc]
  ring

/-- Turning a complex-valued computation of `∑ ‖·‖²` into a real one. -/
