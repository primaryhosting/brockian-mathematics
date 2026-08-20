import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

lemma prodKernel_integral_eq (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    (∫ p : ℝ × ℝ, wt p.1 * wt p.2 * φ (p.1 + p.2) ∂(volume.prod volume))
      = ∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), x * y * φ (x + y) := by
  have hfub : (∫ x : ℝ, ∫ y : ℝ, wt x * wt y * φ (x + y))
      = ∫ p : ℝ × ℝ, wt p.1 * wt p.2 * φ (p.1 + p.2) ∂(volume.prod volume) :=
    integral_integral (integrable_prodKernel hmeas hb)
  rw [← hfub]
  have hinner : ∀ x : ℝ, (∫ y : ℝ, wt x * wt y * φ (x + y))
      = wt x * ∫ y in Ioi (0:ℝ), y * φ (x + y) := by
    intro x
    have hrw : (fun y : ℝ => wt x * wt y * φ (x + y))
        = Set.indicator (Ioi (0:ℝ)) (fun y => wt x * (y * φ (x + y))) := by
      funext y
      rcases lt_or_ge 0 y with h | h
      · rw [wt_of_pos h, indicator_of_mem (mem_Ioi.mpr h)]; ring
      · rw [wt_of_nonpos h, indicator_of_notMem (by simpa using h)]; ring
    rw [hrw, integral_indicator measurableSet_Ioi, integral_const_mul]
  simp_rw [hinner]
  have hrw2 : (fun x : ℝ => wt x * ∫ y in Ioi (0:ℝ), y * φ (x + y))
      = Set.indicator (Ioi (0:ℝ)) (fun x => ∫ y in Ioi (0:ℝ), x * y * φ (x + y)) := by
    funext x
    rcases lt_or_ge 0 x with h | h
    · rw [wt_of_pos h, indicator_of_mem (mem_Ioi.mpr h), ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      ring
    · rw [wt_of_nonpos h, indicator_of_notMem (by simpa using h), zero_mul]
  rw [hrw2, integral_indicator measurableSet_Ioi]

