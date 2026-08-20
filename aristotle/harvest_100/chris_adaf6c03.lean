/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S(p) = -∑ i, p i * log (p i)`. -/
noncomputable def gibbsEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- The set of nonnegative vectors is convex. -/
lemma convex_nonneg_vectors (ι : Type*) : Convex ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} := by
  intro x hx y hy a b ha hb _ i
  have := mul_nonneg ha (hx i)
  have := mul_nonneg hb (hy i)
  simpa using add_nonneg ‹0 ≤ a * x i› ‹0 ≤ b * y i›

/-- Pointwise concavity of `t ↦ -t * log t` on `[0, ∞)`, from
`Real.strictConcaveOn_negMulLog`. -/
lemma negMulLog_concave_pair {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (-(x * Real.log x)) + b * (-(y * Real.log y)) ≤
      -((a * x + b * y) * Real.log (a * x + b * y)) := by
  have h := Real.strictConcaveOn_negMulLog.concaveOn.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy)
    ha hb hab
  simpa only [Real.negMulLog, smul_eq_mul, neg_mul] using h

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave** on the set of nonnegative vectors
(in particular on the probability simplex). -/
theorem entropy_concave (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} (gibbsEntropy (ι := ι)) := by
  refine ⟨convex_nonneg_vectors ι, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [gibbsEntropy, smul_eq_mul, mul_neg, ← neg_add, neg_le_neg_iff, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  have key : ∀ i ∈ Finset.univ,
      (a • x + b • y) i * Real.log ((a • x + b • y) i) ≤
        a * (x i * Real.log (x i)) + b * (y i * Real.log (y i)) := by
    intro i _
    have h := negMulLog_concave_pair (hx i) (hy i) ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [h]
  exact Finset.sum_le_sum key

/-- The Gibbs entropy is concave on the probability simplex itself. -/
theorem entropy_concave_stdSimplex (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ (stdSimplex ℝ ι) (gibbsEntropy (ι := ι)) :=
  (entropy_concave ι).subset (fun _ hp => hp.1) (convex_stdSimplex ℝ ι)

end Chem

