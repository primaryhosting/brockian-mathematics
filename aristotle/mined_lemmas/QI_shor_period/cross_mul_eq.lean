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

theorem cross_mul_eq (N Q m r s p q : ℕ) (hQ : 2 * N ^ 2 ≤ Q) (hr : 0 < r) (hrN : r ≤ N)
    (hq : 0 < q) (hqN : q ≤ N)
    (h1 : |(m : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q))
    (h2 : |(m : ℝ) / Q - (p : ℝ) / q| ≤ 1 / (2 * Q)) :
    s * q = p * r := by
  have hN1 : 0 < N := lt_of_lt_of_le hr hrN
  have hQ0 : 0 < Q := by nlinarith
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiff : |(s : ℝ) / r - (p : ℝ) / q| ≤ 1 / Q := by
    calc |(s : ℝ) / r - (p : ℝ) / q|
        = |((m : ℝ) / Q - (p : ℝ) / q) - ((m : ℝ) / Q - (s : ℝ) / r)| := by ring_nf
      _ ≤ |(m : ℝ) / Q - (p : ℝ) / q| + |(m : ℝ) / Q - (s : ℝ) / r| := abs_sub _ _
      _ ≤ 1 / (2 * Q) + 1 / (2 * Q) := by linarith
      _ = 1 / Q := by field_simp; norm_num
  have hprod : |(s : ℝ) * q - (p : ℝ) * r| ≤ (r * q) / Q := by
    have he : (s : ℝ) * q - (p : ℝ) * r = ((s : ℝ) / r - (p : ℝ) / q) * (r * q) := by field_simp
    rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (r : ℝ) * q)]
    calc |(s : ℝ) / r - (p : ℝ) / q| * (r * q) ≤ (1 / Q) * (r * q) :=
          mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ = (r * q) / Q := by ring
  have hsmall : ((r : ℝ) * q) / Q ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hQR (by norm_num)]
    have hrn : (r : ℝ) ≤ N := by exact_mod_cast hrN
    have hqn : (q : ℝ) ≤ N := by exact_mod_cast hqN
    have hQn : 2 * (N : ℝ) ^ 2 ≤ Q := by exact_mod_cast hQ
    nlinarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) q]
  have hlt : ((|(s * q : ℤ) - (p * r : ℤ)| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs]
    push_cast
    linarith
  have hlt2 : |(s * q : ℤ) - (p * r : ℤ)| < 1 := by exact_mod_cast hlt
  rw [abs_lt] at hlt2
  have : (s * q : ℤ) = (p * r : ℤ) := by omega
  exact_mod_cast this

