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

def dirichlet (bonds : Finset ι) (src tgt : ι → S) (v : S → ℝ) : ℝ :=
  ∑ b ∈ bonds, (v (src b) - v (tgt b)) ^ 2

/-- The squared `ℓ²` norm of a profile `v`. -/
