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

lemma om_pow_sixteen : om ^ (16 : ℕ) = 1 := om_primitiveRoot.pow_eq_one

