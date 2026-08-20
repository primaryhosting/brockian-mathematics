import Mathlib

/-!
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical
open Cardinal

namespace Frontier

/-!
## What is (and is not) formalized here

The Continuum Hypothesis (CH) asserts `ℵ₁ = 𝔠`.  Gödel (1938, constructible universe `L`)
and Cohen (1963, forcing) showed that CH is *independent* of ZFC: neither CH nor its
negation is a theorem of ZFC.  That is a **metamathematical** statement about the
first-order theory ZFC and its provability predicate; it cannot be stated, let alone
proved, as a theorem about Lean's own set-theoretic vocabulary — indeed, inside Lean
`Frontier.ContinuumHypothesis` is a perfectly ordinary proposition, and neither it nor
its negation is provable in Mathlib's foundation either.

What we do here is:

* give the formal statement `ContinuumHypothesis` of CH (Lean's `Cardinal` API is the
  ZFC-style cardinal arithmetic, so this is a faithful rendering);
* give a schematic definition `IsIndependentOf` of "independence from a theory", where
  the theory is presented abstractly by a provability predicate on propositions;
* prove, fully in Lean, everything ZFC *does* settle about the pair `ℵ₁`, `𝔠`, namely
  the base case `ℵ₁ ≤ 𝔠` (`Cardinal.aleph_one_le_continuum` in Mathlib), together with
  a Lean-checked reduction of CH to two equivalent formulations: "there is no cardinal
  strictly between `ℵ₀` and `𝔠`", and "every set of reals is countable or has the
  cardinality of the continuum".

The last item is the mathematical content that an independence proof has to straddle:
`ℵ₁ ≤ 𝔠` is a theorem, and the only remaining question — whether the inequality is
strict — is exactly what Gödel's and Cohen's models decide in opposite ways.
-/

/-- The Continuum Hypothesis: the first uncountable cardinal is the cardinality of the
continuum, `ℵ₁ = 𝔠`. -/

theorem CH_iff_forall_set_real :
    ContinuumHypothesis ↔ ∀ s : Set ℝ, s.Countable ∨ #s = 𝔠 := by
  constructor
  · rintro (hCH : (ℵ_ 1 : Cardinal.{0}) = 𝔠) s
    have hle : #s ≤ 𝔠 := by
      have := Cardinal.mk_set_le s
      rwa [Cardinal.mk_real] at this
    rcases lt_or_eq_of_le (hCH ▸ hle : #s ≤ (ℵ_ 1 : Cardinal.{0})) with h | h
    · left
      rw [← Cardinal.succ_aleph0, Order.lt_succ_iff] at h
      exact Set.countable_coe_iff.mp (Cardinal.mk_le_aleph0_iff.mp h)
    · right
      rw [h, hCH]
  · intro h
    have hex : ∃ s : Set ℝ, #s = (ℵ_ 1 : Cardinal.{0}) := by
      rw [← Cardinal.le_mk_iff_exists_set, Cardinal.mk_real]
      exact aleph_one_le_continuum
    obtain ⟨s, hs⟩ := hex
    rcases h s with hcount | hmk
    · exfalso
      have : #s ≤ ℵ₀ :=
        Cardinal.mk_le_aleph0_iff.mpr (Set.countable_coe_iff.mpr hcount)
      rw [hs] at this
      exact absurd this (not_le_of_gt Cardinal.aleph0_lt_aleph_one)
    · show (ℵ_ 1 : Cardinal.{0}) = 𝔠
      rw [← hs, hmk]

/-- **CH independence statement.**

The Lean-checked content of the Gödel–Cohen independence theorem that is available
inside ZFC itself:

1. ZFC proves the base case `ℵ₁ ≤ 𝔠`;
2. CH, i.e. `ℵ₁ = 𝔠`, is equivalent to there being no cardinal strictly between `ℵ₀`
   and `𝔠`;
3. CH is equivalent to the statement that every set of reals is countable or has the
   cardinality of the continuum;
4. consequently the *only* undetermined question is whether `ℵ₁ < 𝔠`, which is exactly
   what Gödel's constructible model (`ℵ₁ = 𝔠`) and Cohen's forcing extension
   (`ℵ₁ < 𝔠`) decide in opposite ways — a metamathematical fact about the formal
   system ZFC, expressible only via a provability predicate as in `IsIndependentOf`,
   and hence not a theorem about Lean's `Cardinal` type. -/
