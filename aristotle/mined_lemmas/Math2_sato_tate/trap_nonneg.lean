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

lemma trap_nonneg (u v ε x : ℝ) : 0 ≤ trap u v ε x := le_max_left _ _

