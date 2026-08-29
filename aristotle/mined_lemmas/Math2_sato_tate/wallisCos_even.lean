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

lemma wallisCos_even (n : ℕ) : wallisCos (2 * n) = π * (n.centralBinom : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp [wallisCos, Nat.centralBinom]
  | succ k ih =>
      have h : 2 * (k + 1) = 2 * k + 2 := by ring
      have hc : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
          = 2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ k)
      rw [h, wallisCos_rec, ih]
      push_cast
      field_simp
      linear_combination (-2 * 4 ^ k : ℝ) * hc

/-- The moments of the trace `2 cos θ` against the Sato–Tate measure, in terms of Wallis
integrals. -/
