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

theorem cutProb_eq_prob_of_disconnected (M : System V S) {A : Finset V}
    (hA : M.Disconnected A) (s s' : V → S) : M.cutProb A s s' = M.prob s s' := by
  have hN : (Fintype.card (V → S) : ℝ) ≠ 0 := (card_pi_pos (V := V) (S := S)).ne'
  refine Finset.prod_congr rfl fun v _ => ?_
  have hconst : ∀ u : V → S, M.tpm v (glue (part A v) s u) = M.tpm v s := by
    intro u
    by_cases hv : v ∈ A
    · refine hA.1 v hv _ _ fun w hw => ?_
      simp [glue, part, hv, hw]
    · have hv' : v ∈ Aᶜ := Finset.mem_compl.2 hv
      refine hA.2 v hv' _ _ fun w hw => ?_
      simp [glue, part, hv, hw]
  unfold cutTpm
  simp only [fun u => congrFun (hconst u) (s' v)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- For a disconnected system, the effective information of the splitting bipartition is `0`. -/
