/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem statisticsOfSpin_sign (n : ℕ) : (statisticsOfSpin n).sign = (-1 : ℂ) ^ n := by
  unfold statisticsOfSpin
  by_cases h : Even n
  · rw [if_pos h, Statistics.sign, h.neg_one_pow]
  · rw [if_neg h, Statistics.sign, (Nat.not_even_iff_odd.1 h).neg_one_pow]

