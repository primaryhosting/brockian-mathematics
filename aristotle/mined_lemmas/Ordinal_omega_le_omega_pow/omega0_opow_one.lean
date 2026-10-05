/-
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- `ω ^ 1 = ω`, where `ω = Ordinal.omega0` is the first infinite ordinal. -/

theorem omega0_opow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one omega0

/-- `ω ≤ ω ^ 2`, where `ω = Ordinal.omega0` is the first infinite ordinal. -/
