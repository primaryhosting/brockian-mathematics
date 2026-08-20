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
noncomputable def posIndex {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- Diagonalization of the Hermitian form attached to `A`: writing `y = U* x` for the
eigenvector unitary `U` of `A`, the real quadratic form `x ↦ Re (xᴴ A x)` becomes the
weighted sum of squares `∑ i, λ i * ‖y i‖²`. -/
theorem hermitian_form_eq_sum_eigenvalues {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re
      = ∑ i, hA.eigenvalues i *
          Complex.normSq ((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) i) := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set y : Fin d → ℂ := star U *ᵥ x with hy
  have hAe : A = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have h1 : A *ᵥ x = U *ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ y) := by
    conv_lhs => rw [hAe]
    rw [hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h2 : star x ᵥ* U = star y := by
    rw [hy, Matrix.star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [h1, Matrix.dotProduct_mulVec, h2]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hre : ((RCLike.ofReal (hA.eigenvalues i) : ℂ)).re = hA.eigenvalues i := rfl
  have him : ((RCLike.ofReal (hA.eigenvalues i) : ℂ)).im = 0 := rfl
  simp only [Pi.star_apply, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, hre, him]
  ring

/-- **Sylvester's law of inertia** (Hermitian version, the inequality direction used in the
paper): if the Hermitian form `x ↦ Re (xᴴ A x)` of a Hermitian matrix `A` is positive definite
on a complex subspace `W` of `Fin d → ℂ`, then `finrank W ≤ posIndex A`, the number of
strictly positive eigenvalues of `A`. -/
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

