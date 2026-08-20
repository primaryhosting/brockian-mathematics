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

lemma shearKernel_integral_eq (hmeas : Measurable φ)
    (hb : ∀ s, |φ s| ≤ C * Real.exp (-(s/2))) :
    (∫ p : ℝ × ℝ, wt p.1 * wt (p.2 - p.1) * φ p.2 ∂(volume.prod volume))
      = (1/6) * ∫ u in Ioi (0:ℝ), u ^ 3 * φ u := by
  have hfub : (∫ x : ℝ, ∫ u : ℝ, wt x * wt (u - x) * φ u)
      = ∫ p : ℝ × ℝ, wt p.1 * wt (p.2 - p.1) * φ p.2 ∂(volume.prod volume) :=
    integral_integral (integrable_shearKernel hmeas hb)
  rw [← hfub, integral_integral_swap (integrable_shearKernel hmeas hb)]
  have hinner : ∀ u : ℝ, (∫ x : ℝ, wt x * wt (u - x) * φ u) = wt3 u * φ u := by
    intro u
    rw [← integral_wt_conv u, ← integral_mul_const]
  simp_rw [hinner]
  have hrw : (fun u : ℝ => wt3 u * φ u)
      = Set.indicator (Ioi (0:ℝ)) (fun u => (1/6) * (u ^ 3 * φ u)) := by
    funext u
    rcases lt_or_ge 0 u with h | h
    · rw [wt3_of_pos h, indicator_of_mem (mem_Ioi.mpr h)]; ring
    · rw [wt3_of_nonpos h, indicator_of_notMem (by simpa using h), zero_mul]
  rw [hrw, integral_indicator measurableSet_Ioi, integral_const_mul]

/-- **The two-dimensional moment identity.**  For a measurable `φ` with an exponentially
decaying majorant, `∫₀^∞ ∫₀^∞ x y φ(x+y) dy dx = (1/6) ∫₀^∞ u³ φ(u) du`. -/
