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

open MeasureTheory Real Filter Set
open scoped Topology ENNReal Nat

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The density of the Sato–Tate measure with respect to Lebesgue measure on `[0, π]`:
`θ ↦ (2/π) sin²θ`. -/

noncomputable def wallisCos (n : ℕ) : ℝ := ∫ x in (0:ℝ)..π, Real.cos x ^ n

