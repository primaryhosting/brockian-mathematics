/-
  Corpus declarations (reproduced verbatim from the Brockian modules, restricted to
  what is needed) together with the new bridge theorem

      freeSchrodingerPMap ≤ spectralFreeLaplacian.
-/
import Mathlib

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace ENNReal

/-! ## From `Brockian/WeylSchrodingerMinimal.lean` -/

namespace Brockian.Weyl.SchrodingerMinimal

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **The Schwartz core, embedded in `L²`.** -/

private theorem freeSymbolMaximal_apply_fourierSchwartz (f : SchwartzMap ℝ ℂ)
    (v : freeSymbolMaximal.domain) (hv : (v : L2R) = schwartzToL2 (fourierSchwartz f)) :
    freeSymbolMaximal v = -(schwartzToL2 (fourierSchwartz (D2 f))) := by
  apply Lp.ext
  have hmul : (freeSymbolMaximal v : ℝ → ℂ) =ᵐ[volume]
      freeSymbol * ((v : L2R) : ℝ → ℂ) :=
    coeFn_maximalMul (μ := (volume : Measure ℝ)) freeSymbol v
  filter_upwards [hmul, hv ▸ coeFn_schwartzToL2 (fourierSchwartz f),
    Lp.coeFn_neg (schwartzToL2 (fourierSchwartz (D2 f))),
    coeFn_schwartzToL2 (fourierSchwartz (D2 f))] with x e0 e1 e2 e3
  simp only [Pi.mul_apply, Pi.neg_apply] at e0 e1 e2 e3 ⊢
  rw [e0, e1, e2, e3]
  exact freeSymbol_mul_fourierSchwartz f x

