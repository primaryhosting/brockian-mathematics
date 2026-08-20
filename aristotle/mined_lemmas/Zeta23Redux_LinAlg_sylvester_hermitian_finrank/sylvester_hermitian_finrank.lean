import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of a Hermitian matrix: the number of its strictly positive
eigenvalues (counted with multiplicity, i.e. as a cardinality of indices). -/

theorem sylvester_hermitian_finrank {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set S : Finset (Fin d) := Finset.univ.filter fun i => 0 < hA.eigenvalues i with hS
  -- the linear map sending `x ∈ W` to the coordinates, in the eigenbasis, indexed by `S`
  set f : W →ₗ[ℂ] (S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // i ∈ S} → Fin d)).comp
      ((Matrix.mulVecLin (star U)).comp W.subtype) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hfx
    have hzero : ∀ i ∈ S, (star U *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun (Subtype.ext_iff.mp hfx) ⟨i, hi⟩
      simpa [hf, LinearMap.funLeft_apply] using congrFun hfx ⟨i, hi⟩
    have hle : (star x ⬝ᵥ A *ᵥ x).re ≤ 0 := by
      rw [hermitian_form_eq_sum_eigenvalues hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : i ∈ S
      · simp [hzero i hi]
      · have hlam : hA.eigenvalues i ≤ 0 := by
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
          exact hi
        exact mul_nonpos_of_nonpos_of_nonneg hlam (Complex.normSq_nonneg _)
    have hx0 : x = 0 := by
      by_contra hne
      exact absurd hle (not_le.mpr (hW x hx hne))
    exact Subtype.ext hx0
  have := LinearMap.finrank_le_finrank_of_injective (f := f) hinj
  simpa [posIndex, hS, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using this

end Zeta23Redux.LinAlg

