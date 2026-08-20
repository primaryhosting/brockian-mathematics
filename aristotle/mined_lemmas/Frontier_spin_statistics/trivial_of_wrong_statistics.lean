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

theorem trivial_of_wrong_statistics (hwrong : Φ.stat ≠ statisticsOfSpin Φ.twiceSpin)
    (f : TF) : Φ.field f = 0 := by
  -- The sign of the actual statistics differs from `(-1)^{2s}`.
  have hsign : Φ.stat.sign ≠ (-1 : ℂ) ^ Φ.twiceSpin := by
    intro h
    exact hwrong (Statistics.eq_of_sign_eq (by rw [h, statisticsOfSpin_sign]))
  -- Locality plus weak local commutativity kill the two-point function at spacelike
  -- separation.
  have hvanish : ∀ f g : TF, SpacelikeSeparated (Φ.supp f) (Φ.supp g) →
      ⟪Φ.vacuum, (Φ.fieldAdj g) (Φ.field f Φ.vacuum)⟫_ℂ = 0 := by
    intro f g h
    have h1 := Φ.vev_locality h
    have h2 := Φ.jost f g h
    have h3 : (Φ.stat.sign - (-1 : ℂ) ^ Φ.twiceSpin)
        * ⟪Φ.vacuum, (Φ.fieldAdj g) (Φ.field f Φ.vacuum)⟫_ℂ = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) hsign
    · exact h4
  -- Analytic continuation to coincident arguments, then positivity.
  have hzero := Φ.analytic hvanish f
  rw [Φ.vev_normalOrder f] at hzero
  have : ‖Φ.field f Φ.vacuum‖ = 0 := by
    have : ((‖Φ.field f Φ.vacuum‖ : ℂ)) ^ 2 = 0 := hzero
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    exact_mod_cast this
  exact Φ.separating f (by simpa using norm_eq_zero.1 this)

end WightmanField

/-- **The spin–statistics connection.**  A relativistic quantum field satisfying the
Wightman-type axioms packaged in `WightmanField` — locality with respect to its statistics,
weak local commutativity at Jost points, analyticity of the two-point function, and the
Reeh–Schlieder property of the vacuum — which is not identically zero must be quantized
with the statistics dictated by its spin: integer spin fields are bosons (they commute at
spacelike separation) and half-integer spin fields are fermions (they anticommute). -/
