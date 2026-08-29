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

set_option autoImplicit false

namespace Frontier

open Cardinal FirstOrder Language

/-! ## Part 1: the statement of the Continuum Hypothesis

We state CH in two equivalent ways and prove the equivalence inside Lean:

* the *cardinal-arithmetic* form `2 ^ ℵ₀ = ℵ₁` (equivalently `𝔠 = ℵ₁`), and
* the *no intermediate cardinality* form: every set of reals which is uncountable
  has the cardinality of the continuum.
-/

/-- The Continuum Hypothesis, in cardinal-arithmetic form: `𝔠 = ℵ₁`. -/

theorem CH_iff_CHNoIntermediate : CH ↔ CHNoIntermediate := by
  constructor
  · intro h s hs
    have h1 : (ℵ₁ : Cardinal.{0}) ≤ #s := by
      rw [← Cardinal.succ_aleph0]
      exact Order.succ_le_of_lt hs
    have h2 : #s ≤ 𝔠 := by
      have : #s ≤ #ℝ := Cardinal.mk_set_le s
      rwa [Cardinal.mk_real] at this
    exact le_antisymm h2 (h ▸ h1)
  · intro h
    obtain ⟨s, hs⟩ : ∃ s : Set ℝ, #s = ℵ₁ := by
      rw [← Cardinal.le_mk_iff_exists_set, Cardinal.mk_real]
      exact aleph_one_le_continuum
    have hlt : ℵ₀ < #s := by
      rw [hs]
      exact Cardinal.aleph0_lt_aleph_one
    have := h s hlt
    rw [hs] at this
    exact this.symm

/-- CH is equivalent to the cardinal exponentiation statement `2 ^ ℵ₀ = ℵ₁`. -/
