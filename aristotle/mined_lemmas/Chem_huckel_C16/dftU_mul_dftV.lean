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

lemma dftU_mul_dftV : dftU * dftV = 1 := by
  have key : ∀ j l : Fin 16, ((j.val + 15 * l.val) % 16 = 0 ↔ j = l) := by decide
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 16, dftU j k * dftV k l
      = (16 : ℂ)⁻¹ * (om ^ (j.val + 15 * l.val)) ^ (k.val) := by
    intro k
    simp only [dftU, dftV, Matrix.of_apply, om_inv_eq, ← pow_mul]
    rw [mul_comm ((16 : ℂ)⁻¹) _, ← mul_assoc, ← pow_add,
      show j.val * k.val + 15 * (k.val * l.val) = (j.val + 15 * l.val) * k.val from by ring,
      mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_om_pow, Matrix.one_apply]
  by_cases h : j = l
  · rw [if_pos ((key j l).mpr h), if_pos h]; norm_num
  · rw [if_neg (fun hc => h ((key j l).mp hc)), if_neg h]; ring

