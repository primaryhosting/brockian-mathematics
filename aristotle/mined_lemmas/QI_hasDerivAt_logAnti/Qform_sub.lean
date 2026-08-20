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

import RequestProject.QI.Spectral

/-!
# An integral formula for the relative entropy

The elementary scalar identity

`∫_0^∞ (a²/(b + t a) - a/(1 + t)) dt = a (log a - log b)`  (`QI.integral_scalar`)

for `a, b > 0`, combined with the spectral formulas of `RequestProject.QI.Spectral`, gives the
integral representation

`relEntropy ρ σ = ∫_{t ∈ (0, ∞)} (Rval ρ σ t - (tr ρ).re / (1 + t)) dt`

(`QI.relEntropy_eq_integral`) for positive definite `ρ`, `σ`.  Since `Rval` is monotone under
quantum channels, this immediately yields the data-processing inequality.
-/

namespace QI

open Real MeasureTheory Filter Set Matrix
open scoped Topology ComplexOrder BigOperators MatrixOrder

/-! ### The scalar integral -/

/-- The antiderivative of `t ↦ a²/(b + t a) - a/(1 + t)`. -/

private theorem Qform_sub (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) (B : Matrix n n ℂ) :
    Qform ρ σ t B₀ - Qform ρ σ t B = Sform ρ σ t (B₀ - B) := by
  have hL : Lmap ρ σ t B₀ = ρ := hB₀
  have hlin : Lmap ρ σ t (B₀ - B) = Lmap ρ σ t B₀ - Lmap ρ σ t B := by
    simp only [Lmap, Matrix.sub_mul, Matrix.mul_sub, smul_sub]; abel
  -- expand the quadratic form at `B₀ - B`
  have e1 : Sform ρ σ t (B₀ - B) = (Matrix.trace ((B₀ - B)ᴴ * Lmap ρ σ t (B₀ - B))).re :=
    re_trace_Lmap _ _
  have e2 : Matrix.trace ((B₀ - B)ᴴ * Lmap ρ σ t (B₀ - B))
      = Matrix.trace (B₀ᴴ * Lmap ρ σ t B₀) + Matrix.trace (Bᴴ * Lmap ρ σ t B)
        - Matrix.trace (B₀ᴴ * Lmap ρ σ t B) - Matrix.trace (Bᴴ * Lmap ρ σ t B₀) := by
    rw [hlin]
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    abel
  -- the four terms
  have v1 : (Matrix.trace (B₀ᴴ * Lmap ρ σ t B₀)).re = (Matrix.trace (ρ * B₀)).re := by
    rw [hL, trace_conjTranspose_mul hρ]; simp
  have v2 : (Matrix.trace (Bᴴ * Lmap ρ σ t B₀)).re = (Matrix.trace (ρ * B)).re := by
    rw [hL, trace_conjTranspose_mul hρ]; simp
  have v3 : (Matrix.trace (B₀ᴴ * Lmap ρ σ t B)).re = (Matrix.trace (ρ * B)).re := by
    have hs := trace_Lmap_symm hρ hσ (t := t) B₀ B
    have : (Matrix.trace (B₀ᴴ * Lmap ρ σ t B)).re = (Matrix.trace (Bᴴ * Lmap ρ σ t B₀)).re := by
      rw [← hs]; simp
    rw [this, v2]
  have v4 : (Matrix.trace (Bᴴ * Lmap ρ σ t B)).re
      = (Matrix.trace (Bᴴ * σ * B)).re + t * (Matrix.trace (Bᴴ * B * ρ)).re :=
    (re_trace_Lmap B B).symm
  have hQ₀ : Qform ρ σ t B₀ = (Matrix.trace (ρ * B₀)).re := Qform_eq_of_sylvester hρ hB₀
  rw [e1, e2]
  simp only [Complex.sub_re, Complex.add_re]
  rw [v1, v2, v3, v4, hQ₀]
  simp only [Qform]
  ring

end NoDecEq

/-- A solution of the Sylvester equation maximises `Qform`. -/
