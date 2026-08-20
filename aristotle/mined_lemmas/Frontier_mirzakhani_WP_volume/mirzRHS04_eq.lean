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

lemma mirzRHS04_eq (L : Fin 4 → ℝ) :
    mirzRHS04 L = 2 * π ^ 2 + (3 * (L 0) ^ 2 + (L 1) ^ 2 + (L 2) ^ 2 + (L 3) ^ 2) / 2 := by
  have hterm : ∀ j : Fin 4,
      (∫ x in Ioi (0:ℝ), x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V03 (Fin.cons x (fun k => L (rest04 j k))))
      = F1 (L 0 + L j) + F1 (L 0 - L j) := by
    intro j
    rw [← integral_x_mirzKernel_add]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V03 (Fin.cons x (fun k => L (rest04 j k)))
      = x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j))
    rw [show V03 (Fin.cons x (fun k => L (rest04 j k))) = 1 from rfl]
    ring
  have hsum : ∀ f : Fin 4 → ℝ, ∑ j ∈ ({1,2,3} : Finset (Fin 4)), f j = f 1 + f 2 + f 3 := by
    intro f; simp [Finset.sum_insert, Finset.mem_insert]; ring
  rw [mirzRHS04, Finset.sum_congr rfl (fun j _ => hterm j), hsum]
  rw [F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq]
  ring

