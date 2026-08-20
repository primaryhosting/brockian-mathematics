/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem vev_normalOrder (f : TF) :
    ⟪Φ.vacuum, (Φ.fieldAdj f) (Φ.field f Φ.vacuum)⟫_ℂ
      = (‖Φ.field f Φ.vacuum‖ : ℂ) ^ 2 := by
  have h := Φ.adj_spec f (Φ.field f Φ.vacuum) Φ.vacuum
  have h2 : ⟪Φ.vacuum, (Φ.fieldAdj f) (Φ.field f Φ.vacuum)⟫_ℂ
      = conj ⟪(Φ.fieldAdj f) (Φ.field f Φ.vacuum), Φ.vacuum⟫_ℂ := by
    rw [← inner_conj_symm]
  rw [h2, h, inner_self_eq_norm_sq_to_K]
  simp

/-- The vacuum expectation value of the `ε`-(anti)commutator, evaluated using locality. -/
