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

theorem exists_schwartz_of_mem_domain (x : ((freeLaplacian d).domain)) :
    ∃ φ : 𝓢(EuclSpace d, ℂ), x = ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩ := by
  obtain ⟨φ, hφ⟩ := x.2
  exact ⟨φ, Subtype.ext hφ.symm⟩

/-! ### The key "weak equals strong" lemma -/

/-- If `w` and `y` in `L²` satisfy `⟪w, ψ⟫ = ⟪y, symbol * ψ⟫` for every Schwartz function `ψ`,
then `symbol * y = w` almost everywhere. -/
