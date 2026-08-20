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

lemma abs_latticeMag_le_one (d L : ℕ) (β J h : ℝ) : |latticeMag d L β J h| ≤ 1 :=
  abs_gibbsAvg_le_one (continuous_xyEnergy _ _ _ _ _)
    (continuous_cosC.comp (continuous_apply _)) β (fun _ => abs_cosC_le_one _)

/-! ### The Mermin–Wagner theorem -/

/-- **Mermin–Wagner theorem.**  There is no spontaneous breaking of the continuous `O(2)`
symmetry in dimension `d ≤ 2` at any positive temperature.  For the classical XY model in
the box `{0,…,2L}^d` with nonnegative coupling `J`, at inverse temperature `β` (that is, at
any temperature `T = 1/β > 0`), the magnetization at the centre of the box in the presence of
a symmetry breaking field `h ≥ 0` is smaller than any prescribed `ε > 0` as soon as the field
is small enough — and this uniformly in the volume.  In particular the spontaneous
magnetization `lim_{h ↓ 0} lim_{L → ∞} m(β, J, h, L)` vanishes. -/
