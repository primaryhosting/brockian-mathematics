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

lemma satoTateMeasure_frontier_Icc (a b : ℝ) : satoTateMeasure (frontier (Set.Icc a b)) = 0 := by
  have hsub : frontier (Set.Icc a b) ⊆ {a, b} := by
    intro x hx
    have h1 : x ∈ closure (Set.Icc a b) := frontier_subset_closure hx
    have h2 : x ∉ interior (Set.Icc a b) := by
      rw [frontier] at hx; exact hx.2
    rw [closure_Icc] at h1
    rw [interior_Icc] at h2
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h2
    rcases h2 with h | h
    · exact Or.inl (le_antisymm h h1.1)
    · exact Or.inr (le_antisymm h1.2 h)
  refine measure_mono_null hsub ?_
  rw [Set.insert_eq]
  exact measure_union_null (satoTateMeasure_singleton a) (satoTateMeasure_singleton b)

/-- The Frobenius angle attached to a trace of Frobenius `a` at a prime `p`:
`θ_p = arccos (a_p / (2√p))`, where `a_p = p + 1 - #E(𝔽_p)`. -/
