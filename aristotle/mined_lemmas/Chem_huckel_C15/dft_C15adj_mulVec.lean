/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₅`

The eigenvalues of the adjacency matrix of the cycle graph `C₁₅` are exactly the
numbers `2 cos (2πk/15)` for `k = 0, …, 14`.  (In Hückel molecular orbital theory these
are the orbital energies `α + 2β cos(2πk/15)` of a cyclic conjugated system with 15
centres, in units where `α = 0`, `β = 1`.)

The proof diagonalises the (circulant) adjacency matrix using the discrete Fourier
transform on `ZMod 15`.
-/

namespace Chem

open Complex Finset ZMod

/-- The adjacency matrix of the cycle graph `C₁₅`, with vertices indexed by `ZMod 15`:
two vertices are adjacent exactly when they differ by `1`. -/

lemma dft_C15adj_mulVec (v : ZMod 15 → ℂ) (k : ZMod 15) :
    ZMod.dft (C15adj.mulVec v) k
      = ((stdAddChar k : ℂ) + (stdAddChar (-k) : ℂ)) * ZMod.dft v k := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [C15adj_mulVec, smul_eq_mul, mul_add]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v (j - 1)
      = (stdAddChar (-k) : ℂ) * ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v j := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod 15)) _ _ (fun x => ?_)
    simp only [Equiv.subRight_apply]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have e2 : ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v (j + 1)
      = (stdAddChar k : ℂ) * ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v j := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 15)) _ _ (fun x => ?_)
    simp only [Equiv.coe_addRight]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [e1, e2]
  ring

/-- The Fourier mode `j ↦ e(jκ)` is an eigenvector of the adjacency matrix. -/
