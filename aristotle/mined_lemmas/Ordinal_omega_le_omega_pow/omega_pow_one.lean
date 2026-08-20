import Mathlib
/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, so the module docstring above is placed directly after the
single `import Mathlib` line rather than above it.

Note on notation: in current Mathlib, `Ordinal.omega` (`ω_`) denotes the
initial-ordinal indexing function, while the first infinite ordinal `ω` is
`Ordinal.omega0`. The statements below are about the first infinite ordinal,
i.e. `Ordinal.omega0 = Ordinal.omega 0`.
-/

namespace Ordinal

/-- `ω ^ 1 = ω`, for the first infinite ordinal `ω` (`Ordinal.omega0`). -/

theorem omega_pow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`, for the first infinite ordinal `ω` (`Ordinal.omega0`). -/
