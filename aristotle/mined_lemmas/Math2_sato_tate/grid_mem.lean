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

lemma grid_mem {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) : grid n j ∈ Icc 0 Real.pi := by
  refine ⟨grid_nonneg n j, ?_⟩
  rw [← grid_self hn]
  exact grid_mono hj

