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

theorem Qm_mul_Pm : Qm * Pm = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin 14, Qm i k * Pm k j = (14 : ℂ)⁻¹ * zeta (k * (j - i)) := by
    intro k
    show (14 : ℂ)⁻¹ * zeta (-(i * k)) * zeta (k * j) = _
    rw [show k * (j - i) = -(i * k) + k * j by ring, zeta_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, sum_zeta]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (by simpa [sub_eq_zero] using Ne.symm hij), Matrix.one_apply_ne hij]
    ring

