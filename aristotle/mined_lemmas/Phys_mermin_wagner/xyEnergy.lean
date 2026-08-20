/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/

def xyEnergy (bonds : Finset ι) (src tgt : ι → S) (J h : ℝ) (θ : Cfg S) : ℝ :=
  -J * ∑ b ∈ bonds, cosC (θ (src b) - θ (tgt b)) - h * ∑ x, cosC (θ x)

/-- The configuration obtained by rotating the spin at `x` by the angle `v x`. -/
