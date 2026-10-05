/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem numerator_unique (Q r s s' m : ℕ) (hr : 0 < r) (hQ : 0 < Q) (hrQ : 2 * r ≤ Q)
    (h1 : |(m : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q))
    (h2 : |(m : ℝ) / Q - (s' : ℝ) / r| ≤ 1 / (2 * Q)) : s = s' := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrQR : 2 * (r : ℝ) ≤ Q := by exact_mod_cast hrQ
  have hdiff : |(s : ℝ) / r - (s' : ℝ) / r| ≤ 1 / Q := by
    calc |(s : ℝ) / r - (s' : ℝ) / r|
        = |((m : ℝ) / Q - (s' : ℝ) / r) - ((m : ℝ) / Q - (s : ℝ) / r)| := by ring_nf
      _ ≤ |(m : ℝ) / Q - (s' : ℝ) / r| + |(m : ℝ) / Q - (s : ℝ) / r| := abs_sub _ _
      _ ≤ 1 / (2 * Q) + 1 / (2 * Q) := by linarith
      _ = 1 / Q := by field_simp; norm_num
  have hprod : |(s : ℝ) - (s' : ℝ)| ≤ (r : ℝ) / Q := by
    have he : (s : ℝ) - (s' : ℝ) = ((s : ℝ) / r - (s' : ℝ) / r) * r := by field_simp
    rw [he, abs_mul, abs_of_pos hrR]
    calc |(s : ℝ) / r - (s' : ℝ) / r| * r ≤ (1 / Q) * r :=
          mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ = (r : ℝ) / Q := by ring
  have hhalf : (r : ℝ) / Q ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hQR (by norm_num)]
    linarith
  have hlt : ((|(s : ℤ) - (s' : ℤ)| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs]
    push_cast
    linarith
  have hlt2 : |(s : ℤ) - (s' : ℤ)| < 1 := by exact_mod_cast hlt
  rw [abs_lt] at hlt2
  omega

/-! ### The main theorem -/

/-- **Shor's period finding algorithm.**

Let `a` be invertible modulo `N > 1`, let `r` be the multiplicative order of `a`
modulo `N` (the period of `j ↦ a^j mod N`), and run the quantum period-finding
subroutine of Shor's algorithm with a first register of size `Q ≥ 2N²`: prepare
the uniform superposition over `j < Q`, query the oracle `j ↦ a^j mod N`, apply
the quantum Fourier transform modulo `Q` to the first register, and measure it.

Then with probability at least `φ(r)/(16 r)` the observed value `m` determines
the period: the classical continued-fraction post-processing of `m/Q` returns a
reduced fraction with denominator at most `N`, and every such fraction has
denominator exactly `r`. -/
