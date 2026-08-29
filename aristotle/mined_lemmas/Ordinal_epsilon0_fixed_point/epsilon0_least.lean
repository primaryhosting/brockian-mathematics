import Mathlib

/-!
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

open scoped Ordinal

/-- `ε₀`, the least fixed point of ordinal `ω`-exponentiation, as `Ordinal.epsilon 0`. -/
noncomputable abbrev epsilon0 : Ordinal := Ordinal.epsilon 0

/-- **ε₀ is a fixed point of ordinal ω-exponentiation**: `ω ^ ε₀ = ε₀`.
(Here `ω = Ordinal.omega0` is the first infinite ordinal.) -/

theorem epsilon0_least {o : Ordinal} (h : (ω : Ordinal) ^ o = o) : epsilon0 ≤ o :=
  epsilon_zero_le_of_omega0_opow_le h.le

/-- Characterization: `ε₀` is exactly the least ordinal fixed by `ω`-exponentiation. -/
