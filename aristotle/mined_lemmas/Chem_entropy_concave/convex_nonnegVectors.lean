/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` before any module docstring `/-! ... -/`, so the header above
-- uses an ordinary block comment; its text is otherwise verbatim.)

import Mathlib

namespace Chem

open Real Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S p = -∑ i, p i * log (p i)`,
written using `Real.negMulLog`. -/

lemma convex_nonnegVectors (ι : Type*) [Fintype ι] :
    Convex ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} := by
  intro x hx y hy a b ha hb _ i
  have := mul_nonneg ha (hx i)
  have := mul_nonneg hb (hy i)
  simpa using add_nonneg ‹0 ≤ a * x i› ‹0 ≤ b * y i›

/-- **Concavity of the Gibbs entropy.** The map `p ↦ -∑ i, p i * log (p i)` is concave on the
set of vectors with nonnegative entries (in particular on the probability simplex, see
`Chem.entropy_concave_stdSimplex`).  The pointwise ingredient is Mathlib's
`Real.concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici 0) Real.negMulLog`. -/
