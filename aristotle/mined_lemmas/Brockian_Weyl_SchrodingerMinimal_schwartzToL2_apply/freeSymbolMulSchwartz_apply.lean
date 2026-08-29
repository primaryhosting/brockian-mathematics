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

@[simp] theorem freeSymbolMulSchwartz_apply (f : SchwartzMap Real Complex) (xi : Real) :
    freeSymbolMulSchwartz f xi = freeSymbol xi * f xi := by
  rw [freeSymbolMulSchwartz]
  simpa [freeSymbol, Complex.ofReal_mul, Complex.ofReal_pow, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply
      (show (fun xi : Real => (4 * Real.pi ^ 2 * xi ^ 2 : Complex)).HasTemperateGrowth by
        fun_prop) f xi

