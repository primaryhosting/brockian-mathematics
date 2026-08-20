import Brockian.Weyl.FreeLaplacian2

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

/-
Essential self-adjointness of the free Laplacian on `L²(ℝᵈ)`, via the Fourier transform.
-/
import Mathlib

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Function LineDeriv
open scoped FourierTransform ComplexInnerProductSpace Laplacian LinearPMap ContDiff

noncomputable section

variable (d : ℕ)

/-- The configuration space `ℝᵈ`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝᵈ, ℂ)`. -/
abbrev L2 (d : ℕ) := Lp (α := EuclSpace d) ℂ 2

/-- The symbol of the free Laplacian: `-Δ` acts on the Fourier side as multiplication by
`4π²‖ξ‖²`. -/

theorem freeLaplacian_essentiallySelfAdjoint_of_fourier
    (hfourier : ∀ φ : 𝓢(EuclSpace d, ℂ), 𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ)) :
    IsSelfAdjoint ((freeLaplacian d)†) := by
  have hdense : Dense (((freeLaplacian d).domain : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    dense_domain_freeLaplacian d
  have hsym : (freeLaplacian d) ≤ (freeLaplacian d)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense freeLaplacian_isFormalAdjoint_self
  have hdense' : Dense ((((freeLaplacian d)†).domain : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    hdense.mono (fun z hz ↦ hsym.1 hz)
  have h1 : (freeLaplacian d)† ≤ ((freeLaplacian d)†)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense' (adjoint_isFormalAdjoint_self hfourier)
  have hFA : ((freeLaplacian d)†).IsFormalAdjoint (((freeLaplacian d)†)†) :=
    (LinearPMap.adjoint_isFormalAdjoint hdense').symm
  have h2 : ((freeLaplacian d)†)† ≤ (freeLaplacian d)† := by
    refine LinearPMap.IsFormalAdjoint.le_adjoint hdense ?_
    intro x y
    have hx : (x : L2 d) ∈ ((freeLaplacian d)†).domain := hsym.1 x.2
    have h := hFA ⟨(x : L2 d), hx⟩ y
    rw [← h]
    congr 1
    exact hsym.2 (x := x) (y := ⟨(x : L2 d), hx⟩) rfl
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm h2 h1

/-- **The free Laplacian is essentially self-adjoint** (unconditional). -/
