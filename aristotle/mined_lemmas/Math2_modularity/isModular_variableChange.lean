/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the required
-- header appears above as a block comment and is repeated as a docstring below.)

import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open CongruenceSubgroup

namespace Math2

/-- The number of points of the reduction mod `p` of an integral Weierstrass curve,
counted on the affine model together with the point at infinity. -/

lemma isModular_variableChange {E : WeierstrassCurve ℚ} (C : WeierstrassCurve.VariableChange ℚ)
    (h : IsModular E) : IsModular (C • E) := by
  obtain ⟨E₀, C', hC', hmod⟩ := h
  exact ⟨E₀, C * C', by rw [mul_smul, hC'], hmod⟩

/-- **Normalisation to an integral short Weierstrass model.**  Every elliptic curve over `ℚ`
is `ℚ`-isomorphic to an integral short Weierstrass curve `y² = x³ + Ax + B` with
`A B : ℤ` and `4A³ + 27B² ≠ 0`.

The normalisation first puts the curve in short Weierstrass form and then rescales by
`(x, y) ↦ (d² x, d³ y)` to clear denominators. -/
