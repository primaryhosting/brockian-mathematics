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

noncomputable def Pu : (Matrix (Fin 14) (Fin 14) ℂ)ˣ := ⟨Pm, Qm, Pm_mul_Qm, Qm_mul_Pm⟩

/-- **Hückel eigenvalues of the 14-cycle.** The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₄` is `∏ k < 14, (X - 2 cos (2 π k / 14))`; that is, the
adjacency eigenvalues of `C₁₄` are `2 cos (2 π k / 14)` for `k = 0, …, 13`. -/
