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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma eigenvalue_mem (μ : ℂ) (v : ZMod 12 → ℂ) (hv : v ≠ 0) (h : C12adj *ᵥ v = μ • v) :
    ∃ k : ZMod 12, μ = lam k := by
  set w : ZMod 12 → ℂ := Gm *ᵥ v with hw
  have hwne : w ≠ 0 := by
    intro h0
    have : Fm *ᵥ w = 0 := by rw [h0, Matrix.mulVec_zero]
    rw [hw, Matrix.mulVec_mulVec, Fm_mul_Gm] at this
    have h12 : ((12 : ℂ) • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)) *ᵥ v = (12 : ℂ) • v := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h12] at this
    exact hv (by simpa using this)
  have hDw : Dm *ᵥ w = μ • w := by
    rw [hw, Matrix.mulVec_mulVec, ← Gm_mul_C12adj, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_smul]
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hwne (funext hc)
  refine ⟨k, ?_⟩
  have := congrFun hDw k
  have hd : (Dm *ᵥ w) k = lam k * w k := by
    show ∑ j : ZMod 12, (Matrix.diagonal lam) k j * w j = lam k * w k
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Matrix.diagonal_apply] : ∀ j ∈ Finset.univ,
        (Matrix.diagonal lam) k j * w j = (if k = j then lam k else 0) * w j)]
    simp [Finset.sum_ite_eq]
  rw [hd] at this
  exact (mul_right_cancel₀ hk this).symm

