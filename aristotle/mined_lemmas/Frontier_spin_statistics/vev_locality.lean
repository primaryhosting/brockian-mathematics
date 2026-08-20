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

theorem vev_locality {f g : TF} (h : SpacelikeSeparated (Φ.supp f) (Φ.supp g)) :
    ⟪Φ.vacuum, (Φ.field f) (Φ.fieldAdj g Φ.vacuum)⟫_ℂ
      = Φ.stat.sign * ⟪Φ.vacuum, (Φ.fieldAdj g) (Φ.field f Φ.vacuum)⟫_ℂ := by
  have := congrArg (fun A : H →L[ℂ] H => A Φ.vacuum) (Φ.locality f g h)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply] at this
  rw [this, inner_smul_right]

/-- **Wrong statistics forces triviality.**  If a field of spin `s` is quantized with the
statistics *opposite* to the one predicted by the spin–statistics connection, then all its
smeared field operators vanish. -/
