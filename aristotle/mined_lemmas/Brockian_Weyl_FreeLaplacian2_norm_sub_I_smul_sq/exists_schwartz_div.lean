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

theorem exists_schwartz_div (d : ℕ) (c : ℂ) (hc : c.im ≠ 0) {χ : EuclSpace d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ Φ : 𝓢(EuclSpace d, ℂ), ∀ x, Φ x = (χ x : ℂ) / (((freeSymbol d x : ℝ) : ℂ) + c) := by
  have hden : ∀ x : EuclSpace d, ((freeSymbol d x : ℝ) : ℂ) + c ≠ 0 := fun x h =>
    hc (by simpa using congrArg Complex.im h)
  have hg : ContDiff ℝ ∞ (fun x : EuclSpace d => ((freeSymbol d x : ℝ) : ℂ) + c) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_freeSymbol d)).add contDiff_const
  have hsm : ContDiff ℝ ∞
      (fun x : EuclSpace d => (χ x : ℂ) / (((freeSymbol d x : ℝ) : ℂ) + c)) := by
    simp only [div_eq_mul_inv]
    exact (Complex.ofRealCLM.contDiff.comp hχ).mul (hg.inv hden)
  have hcs : HasCompactSupport
      (fun x : EuclSpace d => (χ x : ℂ) / (((freeSymbol d x : ℝ) : ℂ) + c)) := by
    have h1 : HasCompactSupport (fun x : EuclSpace d => (χ x : ℂ)) :=
      hχc.comp_left (g := Complex.ofReal) (by simp)
    have h2 := h1.mul_right (f' := fun x : EuclSpace d => (((freeSymbol d x : ℝ) : ℂ) + c)⁻¹)
    simpa [div_eq_mul_inv] using h2
  exact ⟨hcs.toSchwartzMap hsm, fun x => rfl⟩

/-- The range of `-Δ + c` on Schwartz functions is dense in `L²(ℝ^d)` whenever `c` is not
real; in particular for `c = ± i`. -/
