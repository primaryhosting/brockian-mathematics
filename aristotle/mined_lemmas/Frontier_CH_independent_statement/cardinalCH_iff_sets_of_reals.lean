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

theorem cardinalCH_iff_sets_of_reals :
    CardinalCH ↔ ∀ s : Set ℝ, s.Infinite → #s = ℵ₀ ∨ #s = 𝔠 := by
  constructor
  · intro h s hs
    have h1 : ℵ₀ ≤ #s := Cardinal.infinite_iff.1 hs.to_subtype
    have h2 : #s ≤ 𝔠 := by
      have := Cardinal.mk_set_le s
      rwa [Cardinal.mk_real] at this
    rcases eq_or_lt_of_le h1 with e | lt
    · exact Or.inl e.symm
    · rcases eq_or_lt_of_le h2 with e | lt2
      · exact Or.inr e
      · exact (h _ lt lt2).elim
  · intro h c hc0 hcc
    have hle : c ≤ #ℝ := by rw [Cardinal.mk_real]; exact hcc.le
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.1 hle
    have hinf : s.Infinite :=
      Set.infinite_coe_iff.1 (Cardinal.infinite_iff.2 (hs ▸ hc0.le))
    rcases h s hinf with e | e
    · rw [hs] at e; exact absurd e (ne_of_gt hc0)
    · rw [hs] at e; exact absurd e (ne_of_lt hcc)

/-! ## Part 2: independence, model-theoretically

Mathlib has no proof calculus for first-order logic, but it has the semantic
consequence relation `T ⊨ᵇ φ`, which by Gödel's completeness theorem coincides
with provability from `T`.  "`φ` is independent of `T`" therefore means:
neither `φ` nor `¬ φ` is a semantic consequence of `T`. -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
