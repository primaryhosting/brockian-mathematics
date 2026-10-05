/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module doc comment before the import commands, so the
header is repeated below as a module docstring immediately after the imports.)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the entanglement-entropy area law for one-dimensional gapped systems.

A pure state of a bipartite system `A ⊗ B` is encoded by its coefficient matrix
`M : Matrix A B ℂ` (normalised so that `∑ a b, ‖M a b‖² = 1`).  The reduced density matrix
of the left block is `ρ_A = M Mᴴ`; it is positive semidefinite with unit trace, and the
entanglement entropy of the cut is the von Neumann entropy `-Tr ρ_A log ρ_A`, i.e. the
Shannon entropy of the eigenvalues of `ρ_A` (the squared Schmidt coefficients).

The physical input of Hastings' theorem is that the ground state of a gapped local
1D Hamiltonian is (approximated by) a matrix product state whose bond dimension `D`
depends only on the spectral gap, the local dimension and the interaction strength — and
**not** on the length `L` of the block.  Across a cut, an MPS of bond dimension `D`
factorises the coefficient matrix as `M = X * Y` with an inner index of size `D`.

Everything downstream of that input is proved here from scratch:

* `Phys.shannonEntropy_le_log_of_support` : the maximal-entropy bound
  `H(q) ≤ log N` whenever the probability vector `q` has at most `N` nonzero entries;
* `Phys.card_support_reducedSpectrum` : the number of nonzero eigenvalues of `M Mᴴ`
  equals the rank of `M` (Schmidt rank = matrix rank);
* `Phys.rank_le_of_factorization` : an MPS factorisation through a bond space of
  dimension `D` bounds the rank by `D`;
* `Phys.entanglementEntropy_le_log_rank` : entropy `≤ log (Schmidt rank)`;
* `Phys.area_law_1d` : hence, for a family of cuts admitting a *uniform* bond dimension
  `D`, the entanglement entropy is bounded by the constant `log D`, independently of the
  block length `L`.  This is the area law: in one dimension the boundary of a block has
  `O(1)` sites, and the entropy does not grow with the block volume.

`Phys.uniform_entropy` shows the bound `log D` is attained, and
`Phys.area_law_1d_entropy_density_tendsto_zero` records the resulting sub-volume law.
-/

open scoped BigOperators
open scoped ComplexOrder
open Finset

namespace Phys

/-! ## Shannon entropy of a finite probability vector -/

/-- The Shannon entropy `-∑ qᵢ log qᵢ` of a finitely supported weight vector. -/

theorem entanglementEntropy_le_log_bondDim {D : ℕ} (M : Matrix A B ℂ)
    (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) (X : Matrix A (Fin D) ℂ) (Y : Matrix (Fin D) B ℂ)
    (hXY : M = X * Y) : entanglementEntropy M ≤ Real.log D := by
  refine le_trans (entanglementEntropy_le_log_rank M hM) ?_
  have h1 : (0:ℝ) < (M.rank : ℝ) := by exact_mod_cast one_le_rank M hM
  exact Real.log_le_log h1 (by exact_mod_cast rank_le_of_factorization M X Y hXY)

end Matrices

/-!
## The area law
-/

/--
**Area law for gapped one-dimensional ground states (Hastings).**

Setting: a one-dimensional chain cut into a left block and its complement; the cut labelled
by `L` (say, after `L` sites) has left Hilbert space of dimension `dL L`, right Hilbert
space of dimension `dR L`, and the ground state is described across that cut by its
normalised coefficient matrix `M L`.

Physical input (`hMPS`): Hastings' theorem produces, for a gapped local 1D Hamiltonian, a
bond dimension `D` depending only on the spectral gap, the local dimension and the
interaction strength — and *not* on the block length `L` — such that the ground state is a
matrix product state of bond dimension `D`; across each cut this factorises the coefficient
matrix as `M L = X * Y` through a bond space `Fin D`.  This analytic input (Lieb–Robinson
bounds / AGSP machinery) is taken as a hypothesis; everything else is proved here.

Conclusion: the entanglement entropy of the block is bounded by the constant `log D`,
uniformly in `L`.  Since the boundary of an interval in one dimension consists of `O(1)`
points, this is precisely the area law: the entropy does not grow with the block volume.
-/
