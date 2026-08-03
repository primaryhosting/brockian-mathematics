import Brockian.WeylMaximalMultiplication
import Brockian.WeylSchrodingerGate1Final

/-
Harmonic / Aristotle corrected hard target.

Mathlib's Fourier character is exp(-2*pi*i*x*xi), so the multiplier for the
physical operator -d^2/dx^2 is 4*pi^2*xi^2.  The older unscaled target is
mathematically false.  Statement fidelity is mandatory: do not remove the
4*pi^2 factor, change the Schwartz core, or assume the intertwining conclusion.
-/
namespace Brockian.HardTargets.FreeLaplacianCorrected

open MeasureTheory
open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.SchrodingerGate1Final
open Brockian.Weyl.MaximalMultiplication
open Brockian.Weyl.MaximalMultiplication.Plancherel

noncomputable def freeLaplacianSymbol (xi : Real) : Complex :=
  (4 * Real.pi ^ 2 : Real) * (xi ^ 2 : Complex)

noncomputable def freeLaplacianMultiplier :
    L2R →ₗ.[Complex] L2R :=
  maximalMul (μ := (volume : Measure Real)) freeLaplacianSymbol

/-- The physical free Laplacian is F^{-1} M_{4*pi^2*xi^2} F. -/
noncomputable def correctedFourierDefinedFreeLaplacian :
    L2R →ₗ.[Complex] L2R :=
  conjugatePMap Brockian.FreeLaplacianPlancherel.fourierL2.symm
    freeLaplacianMultiplier

theorem freeLaplacianMultiplier_essentiallySelfAdjoint_target :
    EssentiallySelfAdjoint freeLaplacianMultiplier := by
  sorry

theorem freeSchrodingerPMap_le_correctedFourierDefined_target :
    freeSchrodingerPMap <= correctedFourierDefinedFreeLaplacian := by
  sorry

theorem correctedFourierDefinedFreeLaplacian_essentiallySelfAdjoint_target :
    EssentiallySelfAdjoint correctedFourierDefinedFreeLaplacian := by
  sorry

end Brockian.HardTargets.FreeLaplacianCorrected
