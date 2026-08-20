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

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ## Hückel theory for the cycle `C₁₁`

We compute the spectrum of the adjacency matrix of the cycle graph on 11 vertices by
diagonalising it with the discrete Fourier transform matrix. -/

/-- A primitive 11-th root of unity. -/

lemma Fm_mul_Gm : Fm * Gm = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 11,
      Fm j k * Gm k l = (11 : ℂ)⁻¹ * (om ^ (j.val + 10 * l.val)) ^ k.val := by
    intro k
    simp only [Fm, Gm, ← pow_mul]
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.mul_sum]
  by_cases h : j = l
  · subst h
    have hz : om ^ (j.val + 10 * j.val) = 1 := by
      have h11 : j.val + 10 * j.val = 11 * j.val := by ring
      rw [h11, pow_mul, om_pow_eleven, one_pow]
    rw [hz]
    simp
  · have hz : om ^ (j.val + 10 * l.val) ≠ 1 := by
      intro hc
      have hdvd := (om_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp hc
      have hj := j.isLt
      have hl := l.isLt
      have hjl : j.val ≠ l.val := fun hh => h (Fin.ext hh)
      omega
    have h11 : (om ^ (j.val + 10 * l.val)) ^ 11 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, om_pow_eleven, one_pow]
    rw [sum_pow_eq_zero _ h11 hz]
    simp [h]

