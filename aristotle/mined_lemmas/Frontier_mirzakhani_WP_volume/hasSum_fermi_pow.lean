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

lemma hasSum_fermi_pow (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (-1:ℝ)^n * (x^m * Real.exp (-(((n:ℝ)+1) * x))))
      (x^m / (1 + Real.exp x)) := by
  have hr : ‖(-Real.exp (-x))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-x) < Real.exp 0 := by apply Real.exp_lt_exp.mpr; linarith
    _ = 1 := Real.exp_zero
  have hg := hasSum_geometric_of_norm_lt_one hr
  have h := hg.mul_left (x^m * Real.exp (-x))
  have hex : (0:ℝ) < Real.exp x := Real.exp_pos x
  have key : Real.exp (-x) * (1 + Real.exp (-x))⁻¹ = (1 + Real.exp x)⁻¹ := by
    rw [Real.exp_neg]
    have h2 : (0:ℝ) < 1 + Real.exp x := by positivity
    field_simp
    ring
  have hval : x^m * Real.exp (-x) * (1 - -Real.exp (-x))⁻¹ = x^m / (1 + Real.exp x) := by
    rw [show (1 - -Real.exp (-x)) = 1 + Real.exp (-x) by ring, mul_assoc, key, div_eq_mul_inv]
  rw [hval] at h
  refine h.congr_fun ?_
  intro n
  have hexp : Real.exp (-(((n:ℝ)+1) * x)) = Real.exp (-x) * (Real.exp (-x))^n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  rw [hexp, neg_pow]
  ring

/-- The Dirichlet eta value from the corresponding zeta value:
`∑ (-1)ⁿ/(n+1)^p = (1 - 2^{1-p}) ζ(p)`. -/
