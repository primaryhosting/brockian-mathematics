/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

/-- The Gibbs entropy of a (finite) probability vector `p`, namely `- ∑ i, p i * log (p i)`,
written using `Real.negMulLog x = - x * log x`. -/
noncomputable def gibbsEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

lemma gibbsEntropy_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    gibbsEntropy p = -∑ i, p i * Real.log (p i) := by
  simp [gibbsEntropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- The set of vectors with nonnegative entries. -/
def nonnegOrthant (ι : Type*) : Set (ι → ℝ) := {p | ∀ i, 0 ≤ p i}

lemma convex_nonnegOrthant (ι : Type*) : Convex ℝ (nonnegOrthant ι) := by
  intro x hx y hy a b ha hb _ i
  have := mul_nonneg ha (hx i)
  have := mul_nonneg hb (hy i)
  simpa using add_nonneg ‹0 ≤ a * x i› ‹0 ≤ b * y i›

/-- Each coordinate term `p ↦ negMulLog (p i)` is concave on the nonnegative orthant. -/
lemma concaveOn_coord_negMulLog {ι : Type*} (i : ι) :
    ConcaveOn ℝ (nonnegOrthant ι) (fun p : ι → ℝ => Real.negMulLog (p i)) := by
  have h := Real.strictConcaveOn_negMulLog.concaveOn.comp_linearMap
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)
  refine h.subset (fun p hp => ?_) (convex_nonnegOrthant ι)
  exact hp i

/-- A finite sum of functions concave on a set is concave on that set. -/
lemma concaveOn_finset_sum {ι : Type*} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (t : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ t, ConcaveOn ℝ s (f i)) :
    ConcaveOn ℝ s (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.cons_induction with
  | empty => simpa using (concaveOn_const (0 : ℝ) hs)
  | cons a t ha ih =>
      have hA : ConcaveOn ℝ s (f a) := hf a (Finset.mem_cons_self a t)
      have hB : ConcaveOn ℝ s (fun x => ∑ i ∈ t, f i x) :=
        ih (fun i hi => hf i (Finset.mem_cons_of_mem hi))
      have := hA.add hB
      simpa [Finset.sum_cons, Finset.sum_insert ha, Pi.add_def] using this

/-- The Gibbs entropy is concave on the nonnegative orthant. -/
theorem concaveOn_gibbsEntropy (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ (nonnegOrthant ι) (gibbsEntropy (ι := ι)) := by
  have := concaveOn_finset_sum (convex_nonnegOrthant ι) (Finset.univ : Finset ι)
    (fun i (p : ι → ℝ) => Real.negMulLog (p i))
    (fun i _ => concaveOn_coord_negMulLog i)
  simpa [gibbsEntropy] using this

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector `p`.** -/
theorem entropy_concave (ι : Type*) [Fintype ι] :
    ConcaveOn ℝ (stdSimplex ℝ ι) (gibbsEntropy (ι := ι)) := by
  refine (concaveOn_gibbsEntropy ι).subset (fun p hp => ?_) (convex_stdSimplex ℝ ι)
  exact hp.1

end Chem

