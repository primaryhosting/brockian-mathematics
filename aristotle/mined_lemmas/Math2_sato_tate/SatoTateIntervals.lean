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

def SatoTateIntervals (θ : ℕ → ℝ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ Real.pi →
    Tendsto
      (fun X : ℕ => ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ))
        / (primesBelow X).card)
      atTop (𝓝 (∫ x in α..β, satoTateDensity x))

