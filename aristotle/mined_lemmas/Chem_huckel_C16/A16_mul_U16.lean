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

lemma A16_mul_U16 : A16 * U16 = U16 * Matrix.diagonal lam := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 16) ≠ i + 1 := by
    intro h
    have h3 : (2 : ZMod 16) = 0 := by linear_combination -h
    revert h3; decide
  have key : ∀ j : ZMod 16, A16 i j * U16 j k
      = (if j = i - 1 then U16 j k else 0) + (if j = i + 1 then U16 j k else 0) := by
    intro j
    rw [A16_apply]
    have e1 : (i - j = 1) ↔ (j = i - 1) := by constructor <;> intro h <;> linear_combination -h
    have e2 : (i - j = -1) ↔ (j = i + 1) := by constructor <;> intro h <;> linear_combination -h
    simp only [e1, e2]
    by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;> simp [h1, h2, hne, hne.symm]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => U16 j k),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => U16 j k)]
  simp only [Finset.mem_univ, if_true]
  rw [U16]
  simp only [Matrix.of_apply]
  rw [show (i - 1) * k = i * k + (-k) by ring, show (i + 1) * k = i * k + k by ring,
    ec.map_add_eq_mul, ec.map_add_eq_mul, ← mul_add, add_comm (ec (-k)) (ec k), ec_add_ec_neg]

