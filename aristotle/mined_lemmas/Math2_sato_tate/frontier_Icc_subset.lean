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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma frontier_Icc_subset (α β : ℝ) : frontier (Icc α β) ⊆ {α, β} := by
  intro x hx
  rw [frontier, closure_Icc, interior_Icc] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  simp only [Set.mem_Ioo, not_and, not_lt] at h3
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases eq_or_lt_of_le h1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm h2 (h3 h))

