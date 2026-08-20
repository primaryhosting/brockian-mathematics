import Mathlib
/-!
# Omega Le Omega Pow
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.omega_le_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the header comment above appears just after `import Mathlib`.

namespace Ordinal

/-- `ω ^ 1 = ω`, an instance of the Mathlib lemma `Ordinal.opow_one`. -/

theorem omega_pow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`.  This follows from monotonicity of ordinal exponentiation in the
exponent (`Ordinal.opow_le_opow_right`, which needs `0 < ω`, i.e. `Ordinal.omega0_pos`)
together with `ω ^ 1 = ω` (`Ordinal.opow_one`).

Note: in current Mathlib the ordinal `ω` is called `Ordinal.omega0`
(`Ordinal.omega` denotes the `ω_` indexing function on ordinals). -/
