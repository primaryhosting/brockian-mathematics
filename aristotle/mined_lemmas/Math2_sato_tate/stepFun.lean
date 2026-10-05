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

noncomputable def stepFun (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f Real.pi + ∑ j ∈ Finset.range n,
    (f (grid n j) - f (grid n (j + 1))) * (if x ≤ grid n j then 1 else 0)

