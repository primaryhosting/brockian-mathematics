/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header above is a plain block comment and is repeated as a doc comment below.)

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

/-! ### Values of `cos (2πm/4)` -/

/-- `cos (2πm/4)` only depends on `m % 4`. -/

theorem cos_quarter (m : ℕ) :
    Real.cos (2 * π * m / 4) = Real.cos (2 * π * ((m % 4 : ℕ) : ℝ) / 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4]
  rw [show (2 * π * (((4 * (m / 4) + m % 4 : ℕ)) : ℝ) / 4 : ℝ)
      = 2 * π * ((m % 4 : ℕ) : ℝ) / 4 + (m / 4 : ℕ) * (2 * π) by push_cast; ring]
  exact (Real.cos_periodic.nat_mul _) _

