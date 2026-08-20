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

theorem cutProb_pos_of_prob_pos (M : System V S) (A : Finset V) (s s' : V → S)
    (h : 0 < M.prob s s') : 0 < M.cutProb A s s' := by
  have hfac : ∀ v : V, 0 < M.tpm v s (s' v) := by
    intro v
    rcases (M.tpm_nonneg v s (s' v)).lt_or_eq with hv | hv
    · exact hv
    · exact absurd (Finset.prod_eq_zero (Finset.mem_univ v) hv.symm) h.ne'
  refine Finset.prod_pos fun v _ => ?_
  have hglue : glue (part A v) s s = s := by
    funext w; simp [glue]
  have hle : M.tpm v s (s' v) ≤ ∑ u : V → S, M.tpm v (glue (part A v) s u) (s' v) := by
    have := Finset.single_le_sum
      (f := fun u : V → S => M.tpm v (glue (part A v) s u) (s' v))
      (fun u _ => M.tpm_nonneg _ _ _) (Finset.mem_univ s)
    simpa only [hglue] using this
  exact div_pos (lt_of_lt_of_le (hfac v) hle) (card_pi_pos (V := V) (S := S))

/-- Effective information is always nonnegative. -/
