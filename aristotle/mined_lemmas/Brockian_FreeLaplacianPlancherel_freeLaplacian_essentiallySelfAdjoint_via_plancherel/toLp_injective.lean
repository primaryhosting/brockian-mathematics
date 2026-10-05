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

lemma toLp_injective : Function.Injective (toLpLM (d := d)) := by
  intro f g h
  have hf := f.coeFn_toLp 2 (volume : Measure (Space d))
  have hg := g.coeFn_toLp 2 (volume : Measure (Space d))
  have h' : f.toLp 2 (volume : Measure (Space d)) = g.toLp 2 (volume : Measure (Space d)) := h
  have hae : (f : Space d → ℂ) =ᵐ[volume] (g : Space d → ℂ) := by
    filter_upwards [hf, hg] with x hx hx'
    rw [← hx, ← hx', h']
  exact DFunLike.ext' ((Continuous.ae_eq_iff_eq volume f.continuous g.continuous).mp hae)

/-- The free Laplacian `-Δ` as an unbounded operator on `L²(ℝ^d)` whose domain is the (image in
`L²` of the) Schwartz space. -/
