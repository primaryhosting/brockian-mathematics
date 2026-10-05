/-
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Vaughan Identity
Category: B Brockian Frontier
Target: Brockian.Vaughan.vaughan_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

namespace Brockian
namespace Vaughan

open ArithmeticFunction

/-- The truncation of an arithmetic function to arguments `≤ U`. -/

theorem truncLE_add_truncGT (U : ℕ) (f : ArithmeticFunction ℝ) :
    truncLE U f + truncGT U f = f := by
  ext n
  simp only [ArithmeticFunction.add_apply, truncLE_apply, truncGT_apply]
  rcases le_or_gt n U with h | h
  · simp [h, Nat.not_lt.2 h]
  · simp [h, Nat.not_le.2 h]

/-- **Vaughan's identity**, as an identity of Dirichlet convolutions of arithmetic
functions: for all `U V : ℕ`,
`Λ = truncLE V Λ + truncLE U μ * log - truncLE U μ * truncLE V Λ * ζ
      + truncGT U μ * truncGT V Λ * ζ`. -/
