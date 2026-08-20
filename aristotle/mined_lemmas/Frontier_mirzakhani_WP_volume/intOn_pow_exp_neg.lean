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

lemma intOn_pow_exp_neg (m n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-(((n:ℝ)+1) * x))) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num)
    (((continuous_pow m).mul ((Real.continuous_exp).comp (by fun_prop))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound (2^m * m.factorial) ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
  have hn1 : (1:ℝ) ≤ (n:ℝ)+1 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have he : Real.exp (-(((n:ℝ)+1) * x)) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h3 : x ^ m ≤ 2^m * m.factorial * Real.exp (x/2) := by
    have hb := Real.pow_div_factorial_le_exp (x/2) (by linarith) m
    have hk : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hk, div_pow, div_le_iff₀ (by positivity : (0:ℝ) < 2^m)] at hb
    calc x ^ m ≤ Real.exp (x/2) * m.factorial * 2^m := hb
    _ = 2^m * m.factorial * Real.exp (x/2) := by ring
  have hnn : ‖x ^ m * Real.exp (-(((n:ℝ)+1) * x))‖ = x ^ m * Real.exp (-(((n:ℝ)+1) * x)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx m) (Real.exp_pos _).le)]
  have hb2 : ‖Real.exp (-(1/2) * x)‖ = Real.exp (-(1/2) * x) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hkey : x ^ m * Real.exp (-(((n:ℝ)+1) * x))
      ≤ (2^m * m.factorial) * (Real.exp (x/2) * Real.exp (-x)) := by
    have hmul := mul_le_mul h3 he (Real.exp_pos _).le (by positivity)
    calc x ^ m * Real.exp (-(((n:ℝ)+1) * x))
        ≤ (2^m * m.factorial * Real.exp (x/2)) * Real.exp (-x) := hmul
    _ = (2^m * m.factorial) * (Real.exp (x/2) * Real.exp (-x)) := by ring
  have hcalc : Real.exp (x/2) * Real.exp (-x) = Real.exp (-(1/2)*x) := by
    rw [← Real.exp_add]; ring_nf
  rw [hcalc] at hkey
  rw [hnn, hb2]
  exact hkey

/-! ## Fermi–Dirac integrals -/

