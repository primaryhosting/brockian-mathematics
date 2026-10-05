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

theorem omega_le_omega_pow : (omega0 : Ordinal) ≤ omega0 ^ (2 : Ordinal) := by
  have h : (omega0 : Ordinal) ^ (1 : Ordinal) ≤ omega0 ^ (2 : Ordinal) :=
    opow_le_opow_right omega0_pos (by norm_num)
  rwa [omega_pow_one] at h

/-- Restatement of `ω ≤ ω ^ 2` in terms of `Ordinal.omega 0`, the zeroth entry of the
`ω_` hierarchy, which equals `Ordinal.omega0`. -/
