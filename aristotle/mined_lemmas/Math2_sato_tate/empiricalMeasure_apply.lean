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

open scoped Real ENNReal NNReal Classical
open MeasureTheory Filter Topology Set

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma empiricalMeasure_apply (θ : ℕ → ℝ) (N : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    empiricalMeasure θ N s =
      (N : ℝ≥0∞)⁻¹ * ((Finset.range N).filter fun i => θ i ∈ s).card := by
  simp [empiricalMeasure, Measure.smul_apply, Measure.dirac_apply' _ hs, Set.indicator_apply,
    Finset.sum_boole]

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `θ : ℕ → ℝ` enumerate the Frobenius angles `θ_p = arccos (a_p / (2√p))` of an elliptic
curve without complex multiplication, and let `μs N` be the empirical distribution of the first
`N` of them.  The Sato–Tate conjecture — a theorem of Clozel–Harris–Shepherd-Barron–Taylor for
non-CM curves over `ℚ` (and over totally real fields), whose proof is far beyond what is
currently formalized — states that `μs` converges weakly to the Sato–Tate measure
`(2/π) sin²θ dθ` on `[0, π]`.  This is taken here as the hypothesis `hST`.

The conclusion is the resulting distribution statement: for every subinterval `[a,b] ⊆ [0,π]`,
the proportion of the first `N` Frobenius angles lying in `[a,b]` converges to
`(2/π) ∫_a^b sin²θ dθ = (b - a - (sin b cos b - sin a cos a))/π`. -/
