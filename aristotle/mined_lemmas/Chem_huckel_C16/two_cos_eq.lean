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

lemma two_cos_eq (k : Fin 16) :
    ((2 * Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ) = om ^ k.val + om ^ (15 * k.val) := by
  set x : ℝ := 2 * Real.pi * k.val / 16 with hx
  have h1 : om ^ k.val = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul, hx]
    congr 1
    push_cast
    ring
  have h2 : om ^ (15 * k.val) = Complex.exp (-((x : ℂ) * Complex.I)) := by
    have hmul : om ^ k.val * om ^ (15 * k.val) = 1 := by
      rw [← pow_add, show k.val + 15 * k.val = 16 * k.val from by ring, pow_mul, om_pow_sixteen,
        one_pow]
    rw [(inv_eq_of_mul_eq_one_right hmul).symm, h1, ← Complex.exp_neg]
  rw [h1, h2, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- The entries of the adjacency matrix of `C₁₆`: vertex `j` is adjacent exactly to `j ± 1`. -/
