import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to be the very first command of a file, so the header comment above
is placed immediately after the import.)

## Contents

The Hückel (tight-binding) Hamiltonian of the cyclic polyene `C₁₆` is `α + β A`, where `A` is the
adjacency matrix of the cycle graph `C₁₆`.  We show that the characteristic polynomial of `A`
factors as `∏_{k=0}^{15} (X - 2 cos (2 π k / 16))`, i.e. that the adjacency eigenvalues of `C₁₆`,
listed with multiplicity, are exactly `2 cos (2 π k / 16)` for `k = 0, …, 15`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix built from
the standard additive character `ZMod.stdAddChar` of `ZMod 16`; the orthogonality relation used is
`AddChar.sum_mulShift`, and the invariance of the characteristic polynomial under conjugation comes
from `Matrix.charpoly_mul_comm`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix Polynomial Complex SimpleGraph

/-- The additive character `x ↦ exp (2 π I x / 16)` on `ZMod 16`. -/

lemma ec_add_ec_neg (k : ZMod 16) : ec k + ec (-k) = lam k := by
  set t : ℝ := 2 * Real.pi * k.val / 16 with ht
  have h1 : ec k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [ec_apply, ht]; push_cast; ring_nf
  have hne : ec k ≠ 0 := by rw [h1]; exact Complex.exp_ne_zero _
  have h2 : ec (-k) = (ec k)⁻¹ := by
    have h3 : ec k * ec (-k) = 1 := by
      rw [← ec.map_add_eq_mul, add_neg_cancel, ec.map_zero_eq_one]
    field_simp at h3 ⊢
    linear_combination h3
  rw [h2, h1, ← Complex.exp_neg, lam, ← ht, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

