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

theorem hasSum_alt_zeta_four : HasSum (fun n : ℕ => (-1:ℝ)^n / ((n:ℝ)+1)^4) (7*π^4/720) := by
  have h := hasSum_alt_of_hasSum 4 hasSum_inv_pow_four
  convert h using 1
  norm_num
  ring

/-- The Fermi–Dirac integral `∫₀^∞ x/(1+eˣ) dx = π²/12`. -/
