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

lemma integral_Ioi_linear_shift (c s : ℝ) :
    (∫ y in Ioi c, (y - s)^1 * fd y)
      = (∫ y in Ioi c, y^1 * fd y) - s*(∫ y in Ioi c, y^0 * fd y) := by
  have h0 := intOn_pow_fd 0 c
  have h1 := intOn_pow_fd 1 c
  have hsub : ∀ (f g : ℝ → ℝ), IntegrableOn f (Ioi c) → IntegrableOn g (Ioi c) →
      (∫ y in Ioi c, (f y - g y)) = (∫ y in Ioi c, f y) - ∫ y in Ioi c, g y :=
    fun f g hf hg => integral_sub hf hg
  have hcm : ∀ (a : ℝ) (f : ℝ → ℝ), (∫ y in Ioi c, a * f y) = a * ∫ y in Ioi c, f y :=
    fun a f => integral_const_mul a f
  calc (∫ y in Ioi c, (y - s)^1 * fd y)
      = ∫ y in Ioi c, (y^1 * fd y - s*(y^0 * fd y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro y hy
        show (y - s)^1 * fd y = y^1 * fd y - s*(y^0 * fd y)
        ring
    _ = (∫ y in Ioi c, y^1 * fd y) - ∫ y in Ioi c, s*(y^0 * fd y) :=
        hsub _ _ h1 (h0.const_mul s)
    _ = (∫ y in Ioi c, y^1 * fd y) - s*(∫ y in Ioi c, y^0 * fd y) := by rw [hcm]

/-- Linearity of the shifted third moment. -/
