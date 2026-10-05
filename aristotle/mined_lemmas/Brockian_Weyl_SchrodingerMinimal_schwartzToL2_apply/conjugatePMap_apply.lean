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

theorem conjugatePMap_apply (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H)
    (x : T.domain) :
    conjugatePMap U T (conjugateDomainEquiv U T x) = U (T x) := by
  simp [conjugatePMap, conjugateDomainEquiv]

end Plancherel

end Brockian.Weyl.MaximalMultiplication

/-! ## From `Brockian/FreeLaplacianPlancherel.lean` -/

namespace Brockian.FreeLaplacianPlancherel

open MeasureTheory

/-- `L²(ℝ; ℂ)` with the Lebesgue `volume` measure. -/
noncomputable abbrev L2R : Type := Lp (α := ℝ) ℂ 2

/-- **The Fourier transform on `L²(ℝ; ℂ)` as a concrete unitary.** -/
