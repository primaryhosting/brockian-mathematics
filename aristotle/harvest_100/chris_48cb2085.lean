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
noncomputable def gibbsEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

lemma gibbsEntropy_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    gibbsEntropy p = -∑ i, p i * Real.log (p i) := by
  simp [gibbsEntropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- The set of vectors with nonnegative entries is convex. -/
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
theorem entropy_concave {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} (fun p : ι → ℝ => gibbsEntropy p) := by
  refine ⟨convex_nonnegVectors ι, ?_⟩
  intro x hx y hy a b ha hb hab
  have key : ∀ i ∈ (univ : Finset ι),
      a • Real.negMulLog (x i) + b • Real.negMulLog (y i)
        ≤ Real.negMulLog (a • x i + b • y i) :=
    fun i _ => Real.concaveOn_negMulLog.2 (hx i) (hy i) ha hb hab
  have := Finset.sum_le_sum key
  simpa [gibbsEntropy, smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib] using this

/-- The Gibbs entropy is concave on the probability simplex. -/
theorem entropy_concave_stdSimplex {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ (stdSimplex ℝ ι) (fun p : ι → ℝ => gibbsEntropy p) :=
  entropy_concave.subset (fun _ hp i => hp.1 i) (convex_stdSimplex ℝ ι)

end Chem

import Mathlib

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

