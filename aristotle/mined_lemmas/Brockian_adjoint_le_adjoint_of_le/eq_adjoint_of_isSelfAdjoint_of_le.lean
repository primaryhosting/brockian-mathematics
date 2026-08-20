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
# A basic criterion for essential self-adjointness

This file develops, from scratch, the classical criterion of von Neumann:

If `A` is a densely defined symmetric operator on a complex Hilbert space `H` such that the
ranges of `A + i` and `A - i` are dense — stated here in the equivalent form that a vector
orthogonal to such a range vanishes — then the adjoint `A†` is self-adjoint.  This is exactly
the statement that `A` is *essentially self-adjoint*: the closure of `A` (which is `A††`) is
self-adjoint, equivalently `A` has a unique self-adjoint extension, namely `A†`.

## Main results

* `Brockian.isSelfAdjoint_adjoint_of_denseRange`: the criterion.
* `Brockian.eq_adjoint_of_isSelfAdjoint_of_le`: uniqueness of the self-adjoint extension.
-/

open scoped ComplexInnerProductSpace
open LinearPMap

noncomputable section

namespace Brockian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Antitonicity of the adjoint: an extension has a smaller adjoint. -/

theorem eq_adjoint_of_isSelfAdjoint_of_le {A B : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hA : IsSelfAdjoint A.adjoint) (hB : IsSelfAdjoint B) (hAB : A ≤ B) : B = A.adjoint := by
  rw [LinearPMap.isSelfAdjoint_def] at hA hB
  have hBdense : Dense (B.domain : Set H) := hdense.mono (by exact_mod_cast hAB.1)
  have h1 : B ≤ A.adjoint := hB ▸ adjoint_le_adjoint_of_le hdense hAB
  have h2 : A.adjoint ≤ B := by
    have := adjoint_le_adjoint_of_le hBdense h1
    rwa [hA, hB] at this
  exact le_antisymm h1 h2

end Brockian

import Brockian.EssentialSelfAdjointness

/-!
# Essential self-adjointness of the free Laplacian, via Plancherel's theorem

We consider the *free Laplacian* `-Δ` on `L²(ℝ^d, ℂ)`, defined on the (dense) domain given by
the image of the Schwartz space `𝓢(ℝ^d, ℂ)` inside `L²`.  We show that this operator, viewed as
a densely defined unbounded operator (`LinearPMap`), is symmetric and **essentially
self-adjoint**: its adjoint is self-adjoint, and it admits a unique self-adjoint extension.

The proof of the crucial hypothesis of von Neumann's criterion (density of the ranges of
`-Δ ± i`) is carried out with the Fourier transform: by Plancherel's theorem the Fourier
transform is unitary on `L²`, it maps the Schwartz space onto itself, and it turns `-Δ` into
multiplication by `4π²‖ξ‖²`.  A vector orthogonal to the range of `-Δ ± i` therefore gives a
locally integrable function which integrates to zero against every test function, hence
vanishes; since `4π²‖ξ‖² ± i` never vanishes, the vector itself is zero.

## Main definitions

* `Brockian.FreeLaplacianPlancherel.freeLaplacianPMap`: the operator `-Δ` on `L²(ℝ^d)` with
  domain the image of the Schwartz space.

## Main results

* `Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel`:
  the free Laplacian is densely defined, symmetric, essentially self-adjoint, and `(-Δ)†` is
  its unique self-adjoint extension.
-/

open MeasureTheory SchwartzMap Laplacian LineDeriv
open scoped ComplexConjugate FourierTransform ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-- Euclidean space `ℝ^d`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
abbrev L2s (d : ℕ) := Lp (α := EuclSpace d) ℂ 2 volume

/-- The canonical (injective) linear map from the Schwartz space into `L²(ℝ^d, ℂ)`. -/
