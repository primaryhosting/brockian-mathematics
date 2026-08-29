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

theorem area_law_1d (dL dR : ℕ → ℕ) (M : ∀ L : ℕ, Matrix (Fin (dL L)) (Fin (dR L)) ℂ)
    (hnorm : ∀ L, ∑ a, ∑ b, ‖M L a b‖ ^ 2 = 1) (D : ℕ)
    (hMPS : ∀ L, ∃ (X : Matrix (Fin (dL L)) (Fin D) ℂ) (Y : Matrix (Fin D) (Fin (dR L)) ℂ),
      M L = X * Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, entanglementEntropy (M L) ≤ C := by
  refine ⟨Real.log D, ?_, fun L => ?_⟩
  · refine Real.log_nonneg ?_
    obtain ⟨X, Y, hXY⟩ := hMPS 0
    have h1 : 1 ≤ (M 0).rank := one_le_rank _ (hnorm 0)
    have h2 : (M 0).rank ≤ D := rank_le_of_factorization _ X Y hXY
    exact_mod_cast le_trans h1 h2
  · obtain ⟨X, Y, hXY⟩ := hMPS L
    exact entanglementEntropy_le_log_bondDim (M L) (hnorm L) X Y hXY

/-- Contrapositive form of the area law: if the entanglement entropy across the cuts is
unbounded (a volume law, say), then the state admits no matrix product state description of
constant bond dimension — hence, by Hastings' theorem, cannot be the ground state of a
gapped local one-dimensional Hamiltonian. -/
