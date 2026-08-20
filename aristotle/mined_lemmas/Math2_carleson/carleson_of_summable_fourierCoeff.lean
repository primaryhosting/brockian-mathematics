/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The symmetric partial sum of the Fourier series of `f` at `x`:
`∑_{n = -N}^{N} (fourierCoeff f n) e^{2πinx/T}`. -/

theorem carleson_of_summable_fourierCoeff (f : Lp ℂ 2 (@haarAddCircle T hT))
    (h : Summable (fourierCoeff (f : AddCircle T → ℂ))) :
    ∀ᵐ x ∂(@haarAddCircle T hT),
      Tendsto (fun N => fourierPartialSum (f : AddCircle T → ℂ) N x) atTop
        (𝓝 ((f : AddCircle T → ℂ) x)) := by
  -- The Fourier series sums to a continuous function `g`.
  have hsum : Summable (fun n : ℤ =>
      fourierCoeff (f : AddCircle T → ℂ) n • (fourier n : C(AddCircle T, ℂ))) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourier_norm, mul_one] using h.norm
  obtain ⟨g, hg⟩ := hsum
  -- `g` has the same Fourier coefficients as `f`, hence `f = g` in `L²`.
  have hgLp : HasSum (fun n : ℤ => fourierCoeff (f : AddCircle T → ℂ) n • fourierLp (T := T) 2 n)
      (ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle T hT) ℂ g) := by
    have := ((ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle T hT) ℂ).hasSum hg)
    refine this.congr_fun fun n => ?_
    simp [fourierLp]
  have hfg : ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle T hT) ℂ g = f :=
    hgLp.unique (hasSum_fourier_series_L2 f)
  have hae : (f : AddCircle T → ℂ) =ᵐ[(@haarAddCircle T hT)] (g : AddCircle T → ℂ) := by
    have := ContinuousMap.coeFn_toLp (p := 2) (μ := (@haarAddCircle T hT)) (𝕜 := ℂ) g
    rw [hfg] at this
    exact this
  -- Pointwise, the partial sums converge to `g`.
  have hpt : ∀ x : AddCircle T, Tendsto
      (fun N => fourierPartialSum (f : AddCircle T → ℂ) N x) atTop (𝓝 (g x)) := by
    intro x
    have hx : HasSum (fun n : ℤ => fourierCoeff (f : AddCircle T → ℂ) n • fourier n x) (g x) := by
      simpa using (ContinuousMap.evalCLM ℂ x).hasSum hg
    exact hx.comp tendsto_finset_Icc_atTop
  filter_upwards [hae] with x hx
  rw [hx]
  exact hpt x

/-
Scope note.  Carleson's theorem in its full strength is the statement

