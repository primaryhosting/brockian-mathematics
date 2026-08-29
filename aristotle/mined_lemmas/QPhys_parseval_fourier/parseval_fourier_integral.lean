import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory FourierTransform ComplexInnerProductSpace

namespace QPhys

section General

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Parseval/Plancherel theorem.** The Fourier transform on `L²` preserves inner products:
`⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` for all `f g : L²(E, F)`.  In particular (see
`QPhys.parseval_fourier_norm`) it is an isometry of `L²`. -/

theorem parseval_fourier_integral (f : Lp (α := ℝ) ℂ 2) :
    ∫ x : ℝ, ‖(𝓕 f : ℝ → ℂ) x‖ ^ 2 = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  have h := parseval_fourier_norm (E := ℝ) (F := ℂ) f
  have key : ∀ g : Lp (α := ℝ) ℂ 2,
      ∫ x : ℝ, ‖(g : ℝ → ℂ) x‖ ^ 2 = ‖g‖ ^ 2 := by
    intro g
    have := MeasureTheory.L2.norm_sq_eq_inner (𝕜 := ℂ) g
    have h2 : ⟪g, g⟫ = ∫ x : ℝ, (starRingEnd ℂ) ((g : ℝ → ℂ) x) * (g : ℝ → ℂ) x :=
      MeasureTheory.L2.inner_def g g
    have h3 : ((∫ x : ℝ, ‖(g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) = ⟪g, g⟫ := by
      rw [h2, ← MeasureTheory.integral_complex_ofReal]
      congr 1 with x
      rw [RCLike.star_def, Complex.conj_mul']
      norm_cast
    have h4 : ((∫ x : ℝ, ‖(g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
      rw [h3, this]; norm_num
    exact_mod_cast h4
  rw [key, key, h]

end QPhys

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

