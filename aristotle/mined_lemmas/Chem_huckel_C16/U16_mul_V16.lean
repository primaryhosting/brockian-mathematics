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

lemma U16_mul_V16 : U16 * V16 = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have h : ∀ l : ZMod 16, U16 j l * V16 l k = (16 : ℂ)⁻¹ * ec (l * (j - k)) := by
    intro l
    rw [U16, V16]
    simp only [Matrix.of_apply]
    rw [show ec (j * l) * ((16 : ℂ)⁻¹ * ec (-(l * k)))
          = (16 : ℂ)⁻¹ * (ec (j * l) * ec (-(l * k))) by ring, ← ec.map_add_eq_mul]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun l _ => h l), ← Finset.mul_sum, sum_ec]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.one_apply_eq]
  · rw [if_neg (sub_ne_zero_of_ne hjk), Matrix.one_apply_ne hjk]
    ring

/-- The Fourier matrix diagonalises the adjacency matrix of `C₁₆`. -/
