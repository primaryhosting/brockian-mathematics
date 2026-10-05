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

theorem satoTate_iff_intervals {θ : ℕ → ℝ} (hrange : ∀ p, θ p ∈ Icc 0 Real.pi) :
    SatoTateEquidistributed θ ↔ SatoTateIntervals θ :=
  ⟨fun h _ _ hα hαβ hβ => satoTate_interval h hα hαβ hβ, satoTate_of_intervals hrange⟩


/-! ### A concrete consequence -/

