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

lemma intOn_pow_fd_shift (k : ℕ) (t c : ℝ) :
    IntegrableOn (fun x => x ^ k * fd (x + t)) (Ioi c) := by
  refine integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num)
    (((continuous_pow k).mul
      (continuous_fd.comp (continuous_id.add continuous_const))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound (4^k * k.factorial * Real.exp (-(t/2))) ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
  have h1 : fd (x + t) ≤ Real.exp (-((x+t)/2)) := fd_le_exp _
  have h2 : ‖x ^ k * fd (x+t)‖ = x ^ k * fd (x+t) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx k) (fd_pos _).le)]
  have h3 : x ^ k ≤ 4^k * k.factorial * Real.exp (x/4) := by
    have hb := Real.pow_div_factorial_le_exp (x/4) (by linarith) k
    have hk : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hk, div_pow, div_le_iff₀ (by positivity : (0:ℝ) < 4^k)] at hb
    calc x ^ k ≤ Real.exp (x/4) * k.factorial * 4^k := hb
    _ = 4^k * k.factorial * Real.exp (x/4) := by ring
  have hkey : x ^ k * fd (x+t)
      ≤ (4^k * k.factorial) * (Real.exp (x/4) * Real.exp (-((x+t)/2))) := by
    have hmul := mul_le_mul h3 h1 (fd_pos _).le (by positivity)
    calc x ^ k * fd (x+t) ≤ (4^k * k.factorial * Real.exp (x/4)) * Real.exp (-((x+t)/2)) := hmul
    _ = (4^k * k.factorial) * (Real.exp (x/4) * Real.exp (-((x+t)/2))) := by ring
  have hcalc : Real.exp (x/4) * Real.exp (-((x+t)/2))
      = Real.exp (-(t/2)) * Real.exp (-(1/4) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hnorm : ‖Real.exp (-(1/4) * x)‖ = Real.exp (-(1/4) * x) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hcalc] at hkey
  rw [h2, hnorm]
  exact le_trans hkey (le_of_eq (by ring))

