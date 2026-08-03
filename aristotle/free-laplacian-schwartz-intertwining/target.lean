import Brockian.WeylMaximalMultiplication

/-
Harmonic / Aristotle hard target.

Identify the existing Schwartz-core differential operator with the restriction
of the Plancherel-defined free Laplacian. This is the exact unclosed bridge
between spectral ESA and the concrete action -f''. Constants and Fourier
orientation must match Mathlib's `fourierTransformₗᵢ`; do not weaken the result
to an abstract intertwining hypothesis.
-/
namespace Brockian.HardTargets.FreeLaplacianIntertwining

open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.MaximalMultiplication.Plancherel

noncomputable def freeSchwartzPMap :
    Brockian.Weyl.SchrodingerMinimal.H2 →ₗ.[ℂ]
      Brockian.Weyl.SchrodingerMinimal.H2 :=
  schrodingerPMap (fun _ => 0) (by fun_prop) 0 (by intro x; simp)

theorem freeSchwartzPMap_le_fourierDefinedFreeLaplacian_target :
    freeSchwartzPMap ≤ fourierDefinedFreeLaplacian := by
  sorry

end Brockian.HardTargets.FreeLaplacianIntertwining
