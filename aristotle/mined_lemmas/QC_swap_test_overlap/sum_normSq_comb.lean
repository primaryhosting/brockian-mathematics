/-
/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

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

namespace QC

open Finset

variable {n : ℕ}

/-- The Hermitian inner product `⟨ψ|φ⟩ = ∑ i, conj (ψ i) * φ i` of two vectors of `ℂ^n`. -/

private lemma sum_normSq_comb (psi phi : Fin n → ℂ) (s : ℂ) (hs : s = 1 ∨ s = -1) :
    ((∑ i, ∑ j, Complex.normSq ((psi i * phi j + s * (phi i * psi j)) / 2) : ℝ) : ℂ)
      = ((∑ i, Complex.normSq (psi i) : ℝ) * (∑ i, Complex.normSq (phi i) : ℝ)
          + s * Complex.normSq (overlap psi phi)) / 2 := by
  have hss : s * s = 1 := by rcases hs with h | h <;> simp [h]
  have hconj : (starRingEnd ℂ) s = s := by rcases hs with h | h <;> simp [h]
  push_cast
  have step : ∀ i j : Fin n,
      ((Complex.normSq ((psi i * phi j + s * (phi i * psi j)) / 2) : ℝ) : ℂ)
        = ((starRingEnd ℂ) (psi i) * psi i) * ((starRingEnd ℂ) (phi j) * phi j) / 4
          + s * (((starRingEnd ℂ) (psi i) * phi i) * ((starRingEnd ℂ) (phi j) * psi j)) / 4
          + s * (((starRingEnd ℂ) (phi i) * psi i) * ((starRingEnd ℂ) (psi j) * phi j)) / 4
          + (s * s) * (((starRingEnd ℂ) (phi i) * phi i) * ((starRingEnd ℂ) (psi j) * psi j)) / 4 := by
    intro i j
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_add, map_mul, map_div₀, map_ofNat, hconj]
    ring
  simp only [step, hss, one_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun i _ => by rw [Finset.sum_add_distrib]]
  rw [Finset.sum_congr rfl fun i _ => by rw [Finset.sum_add_distrib]]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (psi i) * psi i) * ((starRingEnd ℂ) (phi j) * phi j) / 4
      = ((∑ i, (starRingEnd ℂ) (psi i) * psi i) * (∑ j, (starRingEnd ℂ) (phi j) * phi j)) / 4 := by
    rw [← sum_sum_mul]
    simp [Finset.sum_div]
  have e2 : ∑ i : Fin n, ∑ j : Fin n,
      s * (((starRingEnd ℂ) (psi i) * phi i) * ((starRingEnd ℂ) (phi j) * psi j)) / 4
      = s * ((∑ i, (starRingEnd ℂ) (psi i) * phi i) * (∑ j, (starRingEnd ℂ) (phi j) * psi j)) / 4 := by
    rw [← sum_sum_mul]
    simp [Finset.sum_div, Finset.mul_sum]
  have e3 : ∑ i : Fin n, ∑ j : Fin n,
      s * (((starRingEnd ℂ) (phi i) * psi i) * ((starRingEnd ℂ) (psi j) * phi j)) / 4
      = s * ((∑ i, (starRingEnd ℂ) (phi i) * psi i) * (∑ j, (starRingEnd ℂ) (psi j) * phi j)) / 4 := by
    rw [← sum_sum_mul]
    simp [Finset.sum_div, Finset.mul_sum]
  have e4 : ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (phi i) * phi i) * ((starRingEnd ℂ) (psi j) * psi j) / 4
      = ((∑ i, (starRingEnd ℂ) (phi i) * phi i) * (∑ j, (starRingEnd ℂ) (psi j) * psi j)) / 4 := by
    rw [← sum_sum_mul]
    simp [Finset.sum_div]
  rw [e1, e2, e3, e4]
  have hp : ∀ f : Fin n → ℂ, ∑ i, (starRingEnd ℂ) (f i) * f i
      = ((∑ i, Complex.normSq (f i) : ℝ) : ℂ) := by
    intro f
    push_cast
    exact Finset.sum_congr rfl fun i _ => (Complex.normSq_eq_conj_mul_self).symm
  rw [hp psi, hp phi]
  have hov : (∑ i, (starRingEnd ℂ) (psi i) * phi i) = overlap psi phi := rfl
  have hov' : (∑ i, (starRingEnd ℂ) (phi i) * psi i) = overlap phi psi := rfl
  rw [hov, hov', ← conj_overlap psi phi]
  rw [Complex.normSq_eq_conj_mul_self]
  push_cast
  ring

/-- **Swap test.** For normalized states `ψ` and `φ` in `ℂ^n`, the swap test accepts (measures
the ancilla qubit in state `|0⟩`) with probability `(1 + |⟨ψ|φ⟩|²)/2`. -/
