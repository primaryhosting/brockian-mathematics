import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Part 1: the Continuum Hypothesis inside Lean's own set theory
-/

open Cardinal

/-- The Continuum Hypothesis, phrased about sets of real numbers:
every infinite set of reals is either countable or of the cardinality of the continuum. -/

theorem continuumHypothesis_iff_aleph_one_eq_continuum :
    ContinuumHypothesis ↔ (ℵ₁ : Cardinal.{0}) = 𝔠 := by
  constructor
  · intro h
    refine le_antisymm Cardinal.aleph_one_le_continuum ?_
    by_contra hlt
    push_neg at hlt
    have h1 : (ℵ₁ : Cardinal.{0}) ≤ #ℝ := by
      rw [Cardinal.mk_real]; exact Cardinal.aleph_one_le_continuum
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.1 h1
    rcases h s (by rw [hs]; exact le_of_lt Cardinal.aleph0_lt_aleph_one) with h2 | h2 <;>
      rw [hs] at h2
    · exact absurd h2 (ne_of_gt Cardinal.aleph0_lt_aleph_one)
    · exact absurd h2 (ne_of_lt hlt)
  · intro h s hs
    by_cases hc : #s = ℵ₀
    · exact Or.inl hc
    · right
      have h1 : ℵ₀ < #s := lt_of_le_of_ne hs (Ne.symm hc)
      have h2 : (ℵ₁ : Cardinal.{0}) ≤ #s := by
        rw [← Cardinal.succ_aleph0]; exact Order.succ_le_of_lt h1
      have h3 : #s ≤ 𝔠 := by
        have := Cardinal.mk_set_le s; rwa [Cardinal.mk_real] at this
      exact le_antisymm h3 (h ▸ h2)

/-- `CH` is equivalent to the statement that no cardinal lies strictly between `ℵ₀` and `𝔠`. -/
