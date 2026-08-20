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

import Mathlib

/-!
# Essential self-adjointness of the free Laplacian

This file proves that the free Laplacian `-Δ`, defined on the Schwartz space
`𝓢(ℝ^d, ℂ)` inside `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

## Formalisation of essential self-adjointness

An unbounded operator is modelled here by a pair of linear maps `ι, A : D →ₗ[ℂ] H`
out of an abstract "domain" module `D`: `ι` is the (dense-range) inclusion of the
operator domain into the Hilbert space `H`, and `A` is the operator itself.

* `Brockian.Weyl.FreeLaplacian2.IsAdjointPair ι A u v` says that `(u, v)` belongs to the graph
  of the adjoint operator `A*`, i.e. `⟪v, ι f⟫ = ⟪u, A f⟫` for all `f` in the domain.
* `Brockian.Weyl.FreeLaplacian2.IsEssentiallySelfAdjoint ι A` says that the domain is dense,
  that `A` is symmetric, and that the adjoint `A*` is symmetric.  For a densely defined
  symmetric operator, symmetry of `A*` is the standard characterisation of essential
  self-adjointness (it is equivalent to `A* = A** = closure of A` being self-adjoint).

The abstract criterion `isEssentiallySelfAdjoint_of_dense_ranges` is von Neumann's basic
criterion: a densely defined symmetric operator with `Ran(A + i)` and `Ran(A - i)` dense is
essentially self-adjoint.

## Main results

* `Brockian.Weyl.FreeLaplacian2.fourier_freeLaplacian`: the Fourier transform conjugates the free
  Laplacian into multiplication by the symbol `4 π² ‖ξ‖²`.
* `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier`: the free
  Laplacian on `𝓢(ℝ^d, ℂ) ⊆ L²(ℝ^d, ℂ)` is essentially self-adjoint.  The statement is
  unconditional: the Fourier-side input is supplied by `fourier_freeLaplacian`.
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Filter Topology
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap ContDiff

noncomputable section

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- `IsAdjointPair ι A u v` states that the pair `(u, v)` belongs to the graph of the adjoint
of the operator `A` with domain `ι`, that is, `⟪v, ι f⟫ = ⟪u, A f⟫` for every `f` in the
domain. -/

theorem fourier_freeLaplacian (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) (x : EuclSpace d) :
    𝓕 (freeLaplacian d f) x = (freeSymbol d x : ℂ) * 𝓕 f x := by
  have key : ∀ (g : 𝓢(EuclSpace d, ℂ)) (m y : EuclSpace d),
      𝓕 (LineDeriv.lineDerivOp m g) y = (2 * π * Complex.I) * (inner ℝ y m : ℝ) * 𝓕 g y := by
    intro g m y
    have h : (fun z : EuclSpace d => (inner ℝ z m : ℝ)).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    simp [SchwartzMap.smulLeftCLM_apply_apply h]
    ring
  have hlap : freeLaplacian d f = -∑ i : Fin d,
      LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f) := by
    simp [freeLaplacian]
  rw [hlap]
  have h2 : 𝓕 (-∑ i : Fin d, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f))
      = -∑ i : Fin d, 𝓕 (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f)) := by
    change (fourierTransformCLM ℂ) _ = _
    rw [map_neg, map_sum]
    rfl
  rw [h2]
  simp only [SchwartzMap.neg_apply, SchwartzMap.sum_apply]
  have h3 : ∀ i : Fin d, 𝓕 (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f)) x
      = -(4 * (π : ℂ) ^ 2) * ((x i : ℝ) : ℂ) ^ 2 * 𝓕 f x := by
    intro i
    rw [key, key]
    simp only [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
    ring_nf
    rw [show Complex.I ^ 2 = -1 from Complex.I_sq]
    ring
  simp only [h3]
  rw [← Finset.sum_mul]
  have h4 : ∑ i : Fin d, (-(4 * (π : ℂ) ^ 2)) * ((x i : ℝ) : ℂ) ^ 2
      = -(4 * (π : ℂ) ^ 2) * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.mul_sum]
    congr 1
    have hnorm : ∑ i : Fin d, (x i) ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [sq_abs]
    push_cast [← hnorm]
    ring
  rw [h4]
  simp only [freeSymbol]
  push_cast
  ring

/-- The inclusion of the Schwartz space into `L²(ℝ^d)`, i.e. the domain of the operator. -/
