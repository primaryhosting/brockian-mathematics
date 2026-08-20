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

