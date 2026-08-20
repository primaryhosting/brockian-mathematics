/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header
-- above is written as a plain block comment.)

import Mathlib

set_option autoImplicit false

open Cardinal FirstOrder Language

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about cardinals

Inside Lean's own (ZFC-like) ambient set theory we can state CH directly:
there is no cardinal strictly between `ℵ₀` and `𝔠 = 2 ^ ℵ₀`.  We check that this
is equivalent to the usual formulation `𝔠 = ℵ₁`, and to the "no set of reals of
intermediate cardinality" formulation.  These equivalences are theorems of ZFC
(they are proved outright below); it is CH itself that is independent. -/

/-- The Continuum Hypothesis, stated for cardinals: no cardinal lies strictly
between `ℵ₀` and the cardinality of the continuum. -/

theorem cardinalCH_iff_continuum_eq_aleph_one :
    CardinalCH ↔ (𝔠 : Cardinal.{0}) = ℵ₁ := by
  constructor
  · intro h
    rcases lt_or_eq_of_le (aleph_one_le_continuum : (ℵ₁ : Cardinal.{0}) ≤ 𝔠) with hlt | heq
    · exact (h ℵ₁ aleph0_lt_aleph_one hlt).elim
    · exact heq.symm
  · intro h c hc0 hcc
    rw [h] at hcc
    have : ℵ₁ ≤ c := by
      rw [← succ_aleph0]
      exact Order.succ_le_of_lt hc0
    exact absurd hcc (not_lt.2 this)

/-- CH is equivalent to: every infinite set of reals is either countable or of the
cardinality of the continuum. -/
