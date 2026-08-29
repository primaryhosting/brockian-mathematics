import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

/-- The Gibbs entropy of a (finite) probability vector `p`, given by `-∑ pᵢ log pᵢ`. -/
noncomputable def gibbsEntropy {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/-- Pointwise reformulation: the entropy is the sum of `Real.negMulLog` over the coordinates. -/
lemma gibbsEntropy_eq_sum_negMulLog {n : ℕ} (p : Fin n → ℝ) :
    gibbsEntropy p = ∑ i, Real.negMulLog (p i) := by
  simp [gibbsEntropy, Real.negMulLog]

/-- The set of nonnegative vectors (containing the probability simplex) is convex. -/
lemma convex_nonneg (n : ℕ) : Convex ℝ {p : Fin n → ℝ | ∀ i, 0 ≤ p i} := by
  intro p hp q hq a b ha hb _ i
  have h₁ : 0 ≤ a * p i := mul_nonneg ha (hp i)
  have h₂ : 0 ≤ b * q i := mul_nonneg hb (hq i)
  simpa using add_nonneg h₁ h₂

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector.**
Stated on the convex set of all nonnegative vectors, which contains the probability simplex. -/
theorem entropy_concave (n : ℕ) :
    ConcaveOn ℝ {p : Fin n → ℝ | ∀ i, 0 ≤ p i}
      (fun p : Fin n → ℝ => -∑ i, p i * Real.log (p i)) := by
  refine ⟨convex_nonneg n, ?_⟩
  intro p hp q hq a b ha hb hab
  have key : ∀ i : Fin n,
      a • Real.negMulLog (p i) + b • Real.negMulLog (q i)
        ≤ Real.negMulLog (a • p i + b • q i) :=
    fun i => Real.strictConcaveOn_negMulLog.concaveOn.2 (hp i) (hq i) ha hb hab
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  have hneg : ∀ r : Fin n → ℝ, -∑ i, r i * Real.log (r i) = ∑ i, Real.negMulLog (r i) := by
    intro r; simp [Real.negMulLog]
  calc a • (fun p : Fin n → ℝ => -∑ i, p i * Real.log (p i)) p
        + b • (fun p : Fin n → ℝ => -∑ i, p i * Real.log (p i)) q
      = ∑ i, (a • Real.negMulLog (p i) + b • Real.negMulLog (q i)) := by
        simp only [hneg]
        rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
    _ ≤ ∑ i, Real.negMulLog (a • p i + b • q i) := hsum
    _ = (fun p : Fin n → ℝ => -∑ i, p i * Real.log (p i)) (a • p + b • q) := by
        simpa using (hneg (a • p + b • q)).symm

end Chem

