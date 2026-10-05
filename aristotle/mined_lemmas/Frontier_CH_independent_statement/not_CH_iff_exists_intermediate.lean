/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

open Cardinal FirstOrder Language

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about sets of reals -/

/-- The Continuum Hypothesis, phrased inside Lean's ambient set theory: every set of reals
that is uncountable has the cardinality of the continuum. -/

theorem not_CH_iff_exists_intermediate :
    ¬ ContinuumHypothesis ↔ ∃ s : Set ℝ, ℵ₀ < #s ∧ #s < 𝔠 := by
  constructor
  · intro h
    simp only [ContinuumHypothesis, not_forall] at h
    obtain ⟨s, hs, hne⟩ := h
    have h1 : #s ≤ 𝔠 := by simpa [Cardinal.mk_real] using Cardinal.mk_set_le s
    exact ⟨s, hs, lt_of_le_of_ne h1 hne⟩
  · rintro ⟨s, hs, hlt⟩ h
    exact absurd (h s hs) hlt.ne

/-! ## Part 2: independence, formalized in first-order logic

Mathlib's `T ⊨ᵇ φ` is the semantic consequence relation; by Gödel's completeness theorem it
coincides with first-order provability, so `IndependentOf T φ` below is the usual notion:
neither `φ` nor its negation is provable from `T`. -/

/-- The first-order language of set theory: no function or constant symbols, and a single
binary relation symbol (membership). -/
