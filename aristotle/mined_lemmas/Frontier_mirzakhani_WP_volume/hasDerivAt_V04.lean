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

lemma hasDerivAt_V04 (L : Fin 4 → ℝ) :
    HasDerivAt (fun x : ℝ => x * V04 (Function.update L 0 x)) (mirzRHS04 L) (L 0) := by
  set S : ℝ := (L 1)^2 + (L 2)^2 + (L 3)^2 with hS
  have hfun : (fun x : ℝ => x * V04 (Function.update L 0 x))
      = fun x : ℝ => 2*π^2*x + x^3/2 + (S/2)*x := by
    funext x
    have hupd : ∑ i, (Function.update L 0 x i)^2 = x^2 + S := by
      rw [Fin.sum_univ_four]
      simp [hS]
      ring
    rw [V04, hupd]
    ring
  rw [hfun, mirzRHS04_eq]
  have h : HasDerivAt (fun x : ℝ => 2*π^2*x + x^3/2 + (S/2)*x)
      (2*π^2 + 3*(L 0)^2/2 + S/2) (L 0) := by
    have h1 : HasDerivAt (fun x : ℝ => 2*π^2*x) (2*π^2) (L 0) := by
      simpa using (hasDerivAt_id (L 0)).const_mul (2*π^2)
    have h2 : HasDerivAt (fun x : ℝ => x^3/2) (3*(L 0)^2/2) (L 0) := by
      simpa using (hasDerivAt_pow 3 (L 0)).div_const 2
    have h3 : HasDerivAt (fun x : ℝ => (S/2)*x) (S/2) (L 0) := by
      simpa using (hasDerivAt_id (L 0)).const_mul (S/2)
    exact (h1.add h2).add h3
  convert h using 1
  rw [hS]; ring

/-- The recursion determines `V_{0,4}` away from `L₁ = 0`. -/
