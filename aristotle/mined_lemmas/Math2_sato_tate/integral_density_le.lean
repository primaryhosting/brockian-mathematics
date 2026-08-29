/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma integral_density_le {u v : ℝ} (huv : u ≤ v) :
    (∫ x in u..v, satoTateDensity x) ≤ 2 / Real.pi * (v - u) := by
  have := integral_density_mul_le huv (φ := fun _ => (1 : ℝ)) continuous_const (fun _ => le_rfl)
  simpa using this

/-! ### Trapezoidal approximations of indicator functions -/

/-- A continuous trapezoidal function which is `1` on `[u+ε, v-ε]` and `0` outside `(u, v)`. -/
