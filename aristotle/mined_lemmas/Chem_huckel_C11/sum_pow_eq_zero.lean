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

lemma sum_pow_eq_zero (z : ℂ) (hz : z ^ 11 = 1) (hne : z ≠ 1) : ∑ k : Fin 11, z ^ k.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 11]
  have h : (∑ i ∈ Finset.range 11, z ^ i) * (z - 1) = 0 := by rw [geom_sum_mul, hz, sub_self]
  rcases mul_eq_zero.mp h with h1 | h2
  · exact h1
  · exact absurd (sub_eq_zero.mp h2) hne

/-- The discrete Fourier transform matrix on `Fin 11`. -/
