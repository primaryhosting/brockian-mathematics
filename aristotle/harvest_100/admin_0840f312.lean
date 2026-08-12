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

namespace Chem

open scoped BigOperators

/-- The Gibbs (Shannon) entropy of a probability vector `p`:
`S(p) = -∑ i, p i * log (p i)`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

lemma entropy_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = -∑ i, p i * Real.log (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- A finite sum of concave functions is concave. -/
lemma concaveOn_finsum {ι : Type*} {E : Type*} [AddCommMonoid E] [Module ℝ E] {s : Set E}
    (hs : Convex ℝ s) (f : ι → E → ℝ) (t : Finset ι)
    (hf : ∀ i ∈ t, ConcaveOn ℝ s (f i)) :
    ConcaveOn ℝ s (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.cons_induction with
  | empty => simpa using concaveOn_const (0 : ℝ) hs
  | cons a t ha ih =>
      simp only [Finset.sum_cons]
      exact (hf a (Finset.mem_cons_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)))

lemma convex_nonneg_vectors (ι : Type*) : Convex ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} := by
  intro x hx y hy a b ha hb _ i
  have hxi : 0 ≤ x i := hx i
  have hyi : 0 ≤ y i := hy i
  have : 0 ≤ a * x i + b * y i := by positivity
  simpa using this

/-- The entropy is concave on the set of vectors with nonnegative entries. -/
theorem entropy_concaveOn_nonneg {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} (entropy (ι := ι)) := by
  have hconv := convex_nonneg_vectors ι
  refine concaveOn_finsum hconv (fun i p => Real.negMulLog (p i)) Finset.univ (fun i _ => ?_)
  exact (Real.concaveOn_negMulLog.comp_linearMap
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).subset (fun p hp => hp i) hconv

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector.** -/
theorem entropy_concave {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ (stdSimplex ℝ ι) (entropy (ι := ι)) :=
  entropy_concaveOn_nonneg.subset (fun _ hp i => hp.1 i) (convex_stdSimplex ℝ ι)

end Chem

#print axioms Chem.entropy_concave

