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

lemma xyEnergy_shift_bound (hJ : 0 ≤ J) (hh : 0 ≤ h) (v : S → ℝ) (θ : Cfg S) :
    xyEnergy bonds src tgt J h (θ + spinWave v)
      + xyEnergy bonds src tgt J h (θ - spinWave v)
      ≤ 2 * xyEnergy bonds src tgt J h θ
        + (J * dirichlet bonds src tgt v + h * sqNorm v) := by
  have hbond : -(dirichlet bonds src tgt v) ≤
      (∑ b ∈ bonds, cosC ((θ + spinWave v) (src b) - (θ + spinWave v) (tgt b)))
      + (∑ b ∈ bonds, cosC ((θ - spinWave v) (src b) - (θ - spinWave v) (tgt b)))
      - 2 * ∑ b ∈ bonds, cosC (θ (src b) - θ (tgt b)) := by
    rw [dirichlet, ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    have e1 : (θ + spinWave v) (src b) - (θ + spinWave v) (tgt b)
        = (θ (src b) - θ (tgt b)) + ((v (src b) - v (tgt b) : ℝ) : Circ) := by
      have hc : ((v (src b) - v (tgt b) : ℝ) : Circ)
          = ((v (src b) : ℝ) : Circ) - ((v (tgt b) : ℝ) : Circ) := rfl
      simp only [Pi.add_apply, spinWave_apply, hc]
      abel
    have e2 : (θ - spinWave v) (src b) - (θ - spinWave v) (tgt b)
        = (θ (src b) - θ (tgt b)) - ((v (src b) - v (tgt b) : ℝ) : Circ) := by
      have hc : ((v (src b) - v (tgt b) : ℝ) : Circ)
          = ((v (src b) : ℝ) : Circ) - ((v (tgt b) : ℝ) : Circ) := rfl
      simp only [Pi.sub_apply, spinWave_apply, hc]
      abel
    rw [e1, e2]
    exact cosC_second_difference _ _
  have hfield : -(sqNorm v) ≤
      (∑ x, cosC ((θ + spinWave v) x)) + (∑ x, cosC ((θ - spinWave v) x))
      - 2 * ∑ x, cosC (θ x) := by
    rw [sqNorm, ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have e1 : (θ + spinWave v) x = θ x + ((v x : ℝ) : Circ) := rfl
    have e2 : (θ - spinWave v) x = θ x - ((v x : ℝ) : Circ) := rfl
    rw [e1, e2]
    exact cosC_second_difference _ _
  unfold xyEnergy
  nlinarith [hbond, hfield, hJ, hh]

end Shift

/-- **Finite–volume Mermin–Wagner bound.**  For the classical XY model with nonnegative
coupling and field, the magnetization at a site `o` is bounded by the energy cost of a
spin-wave profile `v` that rotates the spin at `o` by the angle `π`. -/
