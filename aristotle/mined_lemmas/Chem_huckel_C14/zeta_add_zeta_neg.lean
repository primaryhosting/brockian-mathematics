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

theorem zeta_add_zeta_neg (k : Fin 14) :
    zeta k + zeta (-k) = 2 * (Real.cos (2 * Real.pi * k.val / 14) : ℂ) := by
  have h1 : zeta k * zeta (-k) = 1 := by rw [← zeta_add]; simp [zeta]
  have h2 : zeta (-k) = (zeta k)⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ h1).symm
  rw [h2, zeta_eq_exp, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

/-- The discrete Fourier matrix of order 14. -/
