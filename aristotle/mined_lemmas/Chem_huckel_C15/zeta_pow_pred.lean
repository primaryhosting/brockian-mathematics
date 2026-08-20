/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15

Category: Chemistry.  Target: `Chem.huckel_C15`.

The Hückel (adjacency) eigenvalues of the cycle graph `C₁₅` are `2 cos (2πk/15)`, `k = 0, …, 14`.

The proof diagonalizes the adjacency matrix by the discrete Fourier matrix
`U i k = ζ ^ (k * i)` with `ζ = exp (2πi/15)`, and then uses
`spectrum.units_conjugate` together with `spectrum_diagonal`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/

theorem zeta_pow_pred (k i : Fin 15) :
    zeta ^ (k.val * (i - 1).val) = zeta ^ (k.val * i.val) * (zeta ^ k.val)⁻¹ := by
  have h15 : zeta ^ (15 * k.val) = 1 := by rw [pow_mul, zeta_pow_fifteen, one_pow]
  have key : zeta ^ (k.val * (i - 1).val) = zeta ^ (k.val * i.val + 14 * k.val) := by
    refine zeta_pow_congr ?_
    have h : (i - 1).val ≡ i.val + 14 [MOD 15] := by revert i; decide
    calc k.val * (i - 1).val ≡ k.val * (i.val + 14) [MOD 15] := Nat.ModEq.mul_left _ h
      _ = k.val * i.val + 14 * k.val := by ring
  rw [key, pow_add]
  congr 1
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add]
  have h : 14 * k.val + k.val = 15 * k.val := by ring
  rw [h, h15]

