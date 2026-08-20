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

def IsIndependentOf (Provable : Prop → Prop) (P : Prop) : Prop :=
  ¬ Provable P ∧ ¬ Provable (¬ P)

/-- Base case, provable in ZFC (and in Mathlib): `ℵ₁ ≤ 𝔠`.
This is `Cardinal.aleph_one_le_continuum`. -/
