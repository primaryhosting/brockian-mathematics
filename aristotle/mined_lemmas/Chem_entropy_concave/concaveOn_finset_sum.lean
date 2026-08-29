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
