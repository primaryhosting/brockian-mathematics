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

lemma dftV_mul_dftU : dftV * dftU = 1 := by
  have key : ∀ j l : Fin 16, ((15 * j.val + l.val) % 16 = 0 ↔ j = l) := by decide
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 16, dftV j k * dftU k l
      = (16 : ℂ)⁻¹ * (om ^ (15 * j.val + l.val)) ^ (k.val) := by
    intro k
    simp only [dftU, dftV, Matrix.of_apply, om_inv_eq, ← pow_mul]
    rw [mul_assoc, ← pow_add,
      show 15 * (j.val * k.val) + k.val * l.val = (15 * j.val + l.val) * k.val from by ring]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_om_pow, Matrix.one_apply]
  by_cases h : j = l
  · rw [if_pos ((key j l).mpr h), if_pos h]; norm_num
  · rw [if_neg (fun hc => h ((key j l).mp hc)), if_neg h]; ring

/-- The eigenvalue `2 cos (2πk/16)` written in terms of `om`. -/
