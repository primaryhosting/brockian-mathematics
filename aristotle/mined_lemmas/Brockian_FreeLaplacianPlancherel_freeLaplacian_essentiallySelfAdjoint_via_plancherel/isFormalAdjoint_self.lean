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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` to precede any
-- module docstring; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Laplacian LineDeriv FourierTransform Real LinearPMap
open scoped ComplexConjugate

namespace Brockian.FreeLaplacianPlancherel

/-- Euclidean space `ℝ^d`, the configuration space of the free particle. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
noncomputable abbrev Hs (d : ℕ) := Lp ℂ 2 (volume : Measure (Space d))

variable {d : ℕ}

/-- The symbol (Fourier multiplier) of `-Δ`, namely `4π²‖ξ‖²`. -/

lemma isFormalAdjoint_self : (freeLaplacianPMap d).IsFormalAdjoint (freeLaplacianPMap d) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := hy
  rw [freeLaplacianPMap_apply f, freeLaplacianPMap_apply g]
  exact inner_freeLaplacian_symm f g

