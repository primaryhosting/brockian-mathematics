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

theorem adjMatrix_mul_Pm : (SimpleGraph.cycleGraph 14).adjMatrix ℂ * Pm = Pm * Dm := by
  ext i k
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one i), Dm, Matrix.mul_diagonal]
  show zeta ((i - 1) * k) + zeta ((i + 1) * k) = zeta (i * k) * _
  rw [show (i - 1) * k = i * k + -k by ring, show (i + 1) * k = i * k + k by ring,
    zeta_add, zeta_add, ← mul_add, add_comm (zeta (-k)), zeta_add_zeta_neg]

/-- The discrete Fourier matrix as a unit of the matrix ring. -/
