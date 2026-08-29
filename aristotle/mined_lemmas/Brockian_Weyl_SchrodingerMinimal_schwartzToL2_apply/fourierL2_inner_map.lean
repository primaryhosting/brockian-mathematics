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

theorem fourierL2_inner_map (f g : L2R) :
    (inner ℂ (fourierL2 f) (fourierL2 g)) = inner ℂ f g :=
  (fourierL2).inner_map_map f g

end Brockian.FreeLaplacianPlancherel

/-! ## From `Brockian/WeylFreeLaplacianCorrected.lean` -/

namespace Brockian.Weyl.FreeLaplacianCorrected

open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.SchrodingerGate1Final
open Brockian.Weyl.MaximalMultiplication
open Brockian.Weyl.MaximalMultiplication.Plancherel

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- The physical Fourier symbol for `-d^2/dx^2` under Mathlib's
`exp(-2*pi*i*x*xi)` convention. -/
