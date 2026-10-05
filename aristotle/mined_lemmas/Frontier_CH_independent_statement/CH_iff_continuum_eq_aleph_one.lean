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

theorem CH_iff_continuum_eq_aleph_one :
    ContinuumHypothesis ↔ (𝔠 : Cardinal.{0}) = ℵ_ 1 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (Cardinal.le_mk_iff_exists_set (c := ℵ_ 1) (α := ℝ)).1
      (by simpa [Cardinal.mk_real] using Cardinal.aleph_one_le_continuum)
    have hcont := h s (by rw [hs]; exact Cardinal.aleph0_lt_aleph_one)
    rw [hs] at hcont
    exact hcont.symm
  · intro h s hs
    have h1 : #s ≤ 𝔠 := by simpa [Cardinal.mk_real] using Cardinal.mk_set_le s
    have h2 : ℵ_ 1 ≤ #s := by
      rw [← Cardinal.succ_aleph0]
      exact Order.succ_le_of_lt hs
    rw [h] at h1 ⊢
    exact le_antisymm h1 h2

/-- The negation of the Continuum Hypothesis says exactly that there is a set of reals of
strictly intermediate cardinality. -/
