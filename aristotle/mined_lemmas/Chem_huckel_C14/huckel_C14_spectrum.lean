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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Hückel theory for the cycle graph `C₁₄`

The adjacency eigenvalues of the cycle graph `C₁₄` (the Hückel eigenvalues, in units of the
resonance integral β, of a cyclic conjugated system with 14 centres such as [14]annulene)
are `2 * cos (2 * π * k / 14)` for `k = 0, …, 13`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix
`Pm j k = ζ ^ (j * k)`, where `ζ = exp (2 * π * I / 14)` is a primitive 14-th root of unity.
-/

namespace Chem

open Complex Matrix SimpleGraph Polynomial

attribute [local instance] Fin.instCommRing

/-- A primitive 14-th root of unity. -/

theorem huckel_C14_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) =
      {mu : ℂ | ∃ k : ℕ, k < 14 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)} := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C14, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_range, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero, Set.mem_setOf_eq]

/-- The explicit Hückel molecular orbitals: the vector `j ↦ exp (2 π i j k / 14)` is an
eigenvector of the adjacency matrix of `C₁₄` with eigenvalue `2 cos (2 π k / 14)`. -/
