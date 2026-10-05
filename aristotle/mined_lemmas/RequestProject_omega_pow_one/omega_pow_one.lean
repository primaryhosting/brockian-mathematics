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

theorem omega_pow_one : (omega0 : Ordinal) ^ (1 : Ordinal) = omega0 :=
  opow_one _

/-- `ω ≤ ω ^ 2`, obtained from monotonicity of ordinal exponentiation in the exponent
together with `ω ^ 1 = ω`. -/
