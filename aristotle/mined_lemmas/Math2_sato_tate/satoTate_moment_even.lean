/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Filter Set
open scoped Topology ENNReal Nat

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The density of the Sato–Tate measure with respect to Lebesgue measure on `[0, π]`:
`θ ↦ (2/π) sin²θ`. -/

lemma satoTate_moment_even (n : ℕ) :
    ∫ θ, (2 * Real.cos θ) ^ (2 * n) ∂satoTateMeasure = (catalan n : ℝ) := by
  have hpi : (0:ℝ) < π := pi_pos
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h1 : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (succ_mul_catalan_eq_centralBinom n)
  have h2 : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
      = 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ n)
  have h3 : 2 * n + 2 = 2 * (n + 1) := by ring
  have h4 : (2:ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  rw [satoTate_moment, wallisCos_even, h3, wallisCos_even, h4]
  have expand : 2 / π * 4 ^ n * (π * (Nat.centralBinom n : ℝ) / 4 ^ n
      - π * (Nat.centralBinom (n + 1) : ℝ) / 4 ^ (n + 1))
      = 2 * (Nat.centralBinom n : ℝ) - (Nat.centralBinom (n + 1) : ℝ) / 2 := by
    have h4' : (4:ℝ) ^ n ≠ 0 := by positivity
    field_simp
    ring
  rw [expand]
  refine mul_left_cancel₀ hn ?_
  linear_combination -h1 - (1/2 : ℝ) * h2

/-- The odd moments of the Sato–Tate distribution vanish. -/
