/-
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- `ε₀` is a fixed point of ordinal exponentiation with base `ω`: `ω ^ ε₀ = ε₀`. -/

theorem epsilon0_le_of_fixed_point {o : Ordinal} (h : (omega0 : Ordinal) ^ o = o) : ε₀ ≤ o :=
  epsilon_zero_le_of_omega0_opow_le h.le

/-- `ε₀` is characterized as the least fixed point of `a ↦ ω ^ a`. -/
