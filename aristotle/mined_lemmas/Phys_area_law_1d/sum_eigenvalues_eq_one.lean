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

theorem sum_eigenvalues_eq_one {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : Matrix A B ℂ) (hM : ∑ a, ∑ b, ‖M a b‖ ^ 2 = 1) :
    ∑ i, (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i = 1 := by
  have htr := (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.trace_eq_sum_eigenvalues
  have h2 : (M * Mᴴ).trace = ((∑ a, ∑ b, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [htr, hM] at h2
  have h3 : ((∑ i, (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian.eigenvalues i : ℝ) : ℂ)
      = ((1 : ℝ) : ℂ) := by push_cast; simpa using h2
  exact_mod_cast h3

/-- The number of non-zero eigenvalues of the reduced density matrix equals the Schmidt rank. -/
