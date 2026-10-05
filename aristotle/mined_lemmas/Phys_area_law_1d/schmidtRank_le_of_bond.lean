/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

A pure state of a bipartite quantum system `A ⊗ B` is described, in a product basis, by its
amplitude matrix `M : Matrix A B ℂ`, normalised so that `∑ a b, ‖M a b‖ ^ 2 = 1`.  The reduced
density matrix of the left half is `ρ_A = M * Mᴴ`, and the *entanglement entropy* across the cut
is the von Neumann entropy `-Tr ρ_A log ρ_A = ∑ᵢ negMulLog λᵢ` of its eigenvalues.

The entanglement *area law* in one dimension says that for a gapped local Hamiltonian the ground
state's entanglement entropy across a cut of the chain is bounded by a constant that does not grow
with the length of the chain (the "area" of a cut of a 1D chain being a single point).  The
mechanism, which is the content of Hastings' theorem, is that the gap forces the Schmidt rank
(equivalently, the matrix–product bond dimension) across the cut to be bounded by a constant `D`
independent of the system size.

Here we formalise the area law given that input: from a uniform bound `D` on the Schmidt rank
across the cut we derive the uniform entropy bound `log D`, valid for every chain length.  The
final theorem `Phys.area_law_1d` is stated for a family of chain states indexed by the number of
sites, and its conclusion is a bound that is *independent of the number of sites*.

Note on the file header: it is written as a plain block comment `/- ... -/` rather than a module
docstring `/-! ... -/`, because Lean requires all `import` commands to come before any module
docstring, so a `/-! ... -/` header on line 1 would make the file fail to compile.
-/

open scoped BigOperators ComplexOrder
open Finset Matrix

namespace Phys

/-- The entanglement entropy across a cut, computed from the amplitude matrix `M` of the state:
the von Neumann entropy `∑ᵢ -λᵢ log λᵢ` of the reduced density matrix `ρ = M * Mᴴ`. -/

theorem schmidtRank_le_of_bond {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] (D : ℕ)
    (X : Matrix A (Fin D) ℂ) (Y : Matrix (Fin D) B ℂ) :
    schmidtRank (X * Y) ≤ D := by
  refine (Matrix.rank_mul_le_left X Y).trans ?_
  simpa using X.rank_le_card_width

/-- **Entanglement area law in one dimension.**

`M n` is the amplitude matrix, across a fixed cut, of the ground state of a chain of `n` sites of
local dimension `d` (`hnorm n` says the state is normalised).  The gapped-ness of the model enters
through `hbond`: the Schmidt rank across the cut is bounded by a constant `D`, uniformly in the
chain length `n` — this is the content of Hastings' theorem.  The conclusion is the area law: the
entanglement entropy across the cut is bounded by `log D`, a constant *independent of the number
of sites* (rather than growing with the size of the subsystem). -/
