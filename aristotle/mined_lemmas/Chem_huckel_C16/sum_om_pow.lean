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

/-!
# Hückel theory for the cyclic polyene C₁₆

The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of an annulene with
16 carbon atoms, up to the usual affine normalisation `α + β x`) has characteristic
polynomial `∏ k < 16, (X - 2 cos (2πk/16))`, so its eigenvalues are exactly the
numbers `2 cos (2πk/16)` for `k = 0, …, 15`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix
`U j k = ω^(jk)`, where `ω = exp (2πi/16)`.
-/

namespace Chem

open Polynomial Matrix Complex

/-- The adjacency (Hückel) matrix of the cycle graph `C₁₆`, over `ℂ`. -/

lemma sum_om_pow (m : ℕ) :
    ∑ k : Fin 16, (om ^ m) ^ (k.val) = if m % 16 = 0 then (16 : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (om ^ m) ^ i) 16]
  by_cases h : m % 16 = 0
  · have h1 : om ^ m = 1 := by rw [om_pow_mod m, h, pow_zero]
    simp [h1, h]
  · have hz : om ^ m ≠ 1 := by
      intro hc
      have hdvd : 16 ∣ m := om_primitiveRoot.dvd_of_pow_eq_one m hc
      omega
    rw [geom_sum_eq hz]
    have h16 : (om ^ m) ^ 16 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, om_pow_sixteen, one_pow]
    simp [h16, h]

