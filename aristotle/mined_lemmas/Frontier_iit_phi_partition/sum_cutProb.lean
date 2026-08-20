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

namespace Frontier

/-! ## Gibbs' inequality (nonnegativity of relative entropy) -/

/-- Gibbs' inequality on a finite index type: the relative entropy (Kullback–Leibler
divergence) of two probability distributions is nonnegative, provided `p` is absolutely
continuous with respect to `q`. -/

theorem sum_cutProb (M : System V S) (A : Finset V) (s : V → S) :
    ∑ s' : V → S, M.cutProb A s s' = 1 := by
  have h : ∑ s' : V → S, (∏ v, M.cutTpm (part A v) v s (s' v))
      = ∏ v, ∑ t, M.cutTpm (part A v) v s t := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [cutProb, h, M.sum_cutTpm]

/-- Absolute continuity: the cut dynamics can do everything the actual dynamics can. -/
