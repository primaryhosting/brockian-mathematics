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

lemma hasDerivAt_V05 (L : Fin 5 → ℝ) :
    HasDerivAt (fun x : ℝ => x * V05 (Function.update L 0 x)) (mirzRHS05 L) (L 0) := by
  set Q : ℝ := (L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2 with hQ
  set R : ℝ := (L 1)^4 + (L 2)^4 + (L 3)^4 + (L 4)^4 with hR
  have hfun : (fun x : ℝ => x * V05 (Function.update L 0 x))
      = fun x : ℝ => x^5/8 + (Q/2 + 3*π^2) * x^3
          + (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) * x := by
    funext x
    have h2 : ∑ i, (Function.update L 0 x i)^2 = x^2 + Q := by
      rw [Fin.sum_univ_five]; simp [hQ]; ring
    have h4 : ∑ i, (Function.update L 0 x i)^4 = x^4 + R := by
      rw [Fin.sum_univ_five]; simp [hR]; ring
    rw [V05, h2, h4]
    ring
  rw [hfun, mirzRHS05_eq]
  have h : HasDerivAt (fun x : ℝ => x^5/8 + (Q/2 + 3*π^2) * x^3
      + (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) * x)
      (5*(L 0)^4/8 + (Q/2 + 3*π^2) * (3*(L 0)^2) + (3*π^2*Q + Q^2/4 - R/8 + 10*π^4)) (L 0) := by
    have h1 : HasDerivAt (fun x : ℝ => x^5/8) (5*(L 0)^4/8) (L 0) := by
      simpa using (hasDerivAt_pow 5 (L 0)).div_const 8
    have h2 : HasDerivAt (fun x : ℝ => (Q/2 + 3*π^2) * x^3) ((Q/2 + 3*π^2) * (3*(L 0)^2)) (L 0) := by
      simpa using (hasDerivAt_pow 3 (L 0)).const_mul (Q/2 + 3*π^2)
    have h3 : HasDerivAt (fun x : ℝ => (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) * x)
        (3*π^2*Q + Q^2/4 - R/8 + 10*π^4) (L 0) := by
      simpa using (hasDerivAt_id (L 0)).const_mul (3*π^2*Q + Q^2/4 - R/8 + 10*π^4)
    exact (h1.add h2).add h3
  convert h using 1
  rw [hQ, hR]; ring

/-- The recursion determines `V_{0,5}` away from `L₁ = 0`. -/
