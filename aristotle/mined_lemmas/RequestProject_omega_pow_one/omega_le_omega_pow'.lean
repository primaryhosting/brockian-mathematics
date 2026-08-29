import Mathlib

/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace RequestProject

open Ordinal

/-- `ω ^ 1 = ω`, where `ω = Ordinal.omega0` is the first infinite ordinal.
(In current Mathlib the name `Ordinal.omega` denotes the `ω_` indexing order embedding;
the ordinal `ω` itself is `Ordinal.omega0 = Ordinal.omega 0`.) -/

theorem omega_le_omega_pow' : Ordinal.omega 0 ≤ Ordinal.omega 0 ^ (2 : Ordinal) := by
  rw [Ordinal.omega_zero]
  exact omega_le_omega_pow

/-- Restatement of `ω ^ 1 = ω` in terms of `Ordinal.omega 0`. -/
