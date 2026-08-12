/-
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The positive index of inertia of a Hermitian matrix `A`: the number of indices `i` at which
the eigenvalue function `hA.eigenvalues` is strictly positive (i.e. the number of strictly
positive eigenvalues of `A`, counted with multiplicity). -/
noncomputable def posIndex (hA : A.IsHermitian) : ℕ :=
  Finset.univ.filter (fun i => 0 < hA.eigenvalues i) |>.card

/-- The Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` of a Hermitian matrix `A`, expressed in the
orthonormal eigenbasis of `A`: it is the weighted sum of the squared moduli of the coordinates,
with weights the eigenvalues. -/
theorem re_star_dotProduct_mulVec_eq_sum (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re
      = ∑ i, hA.eigenvalues i *
          ‖(inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x) : ℂ)‖ ^ 2 := by
  have hsym : (Matrix.toLpLin 2 2 A).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hT : ∀ i, (Matrix.toLpLin 2 2 A) (hA.eigenvectorBasis i)
      = (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    intro i
    apply WithLp.ofLp_injective (p := 2)
    show A *ᵥ (WithLp.ofLp (hA.eigenvectorBasis i)) = _
    rw [hA.mulVec_eigenvectorBasis i]
    simp
  have h1 : (star x ⬝ᵥ A *ᵥ x)
      = inner ℂ (WithLp.toLp 2 x) ((Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x)) := by
    rw [show (Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x) = WithLp.toLp 2 (A *ᵥ x) from rfl,
      EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have h3 : (inner ℂ (WithLp.toLp 2 x) ((Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x)) : ℂ)
      = ∑ i, (hA.eigenvalues i : ℂ) *
          ((‖(inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x)
      ((Matrix.toLpLin 2 2 A) (WithLp.toLp 2 x))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsym (hA.eigenvectorBasis i) (WithLp.toLp 2 x), hT i, inner_smul_left,
      Complex.conj_ofReal]
    have hc : (inner ℂ (WithLp.toLp 2 x) (hA.eigenvectorBasis i) : ℂ)
        = starRingEnd ℂ (inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x)) :=
      (inner_conj_symm _ _).symm
    rw [hc]
    set z : ℂ := inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x)
    have h : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; norm_cast
    calc (starRingEnd ℂ) z * ((hA.eigenvalues i : ℂ) * z)
        = (hA.eigenvalues i : ℂ) * ((starRingEnd ℂ) z * z) := by ring
      _ = _ := by rw [h]
  rw [h1, h3, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- The linear map sending a vector to its coordinates, in the eigenbasis of the Hermitian
matrix `A`, along the eigenvectors with strictly positive eigenvalue. -/
noncomputable def posCoords (hA : A.IsHermitian) :
    (Fin d → ℂ) →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) where
  toFun x := fun i => inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x)
  map_add' x y := by
    funext i
    simp
  map_smul' c x := by
    funext i
    simp

/-- **Sylvester's law of inertia** (Hermitian version, the inequality used in the paper):
if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` attached to a Hermitian matrix `A` is positive
definite on a complex subspace `W` of `Fin d → ℂ`, then `finrank W` is at most the positive index
of inertia of `A` (the number of strictly positive eigenvalues of `A`). -/
theorem sylvester_hermitian_finrank (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  have hinj : Function.Injective ⇑((posCoords hA).comp W.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hzero : ∀ i : Fin d, 0 < hA.eigenvalues i →
        (inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x) : ℂ) = 0 := by
      intro i hi
      simpa [posCoords] using
        congrFun (show ((posCoords hA).comp W.subtype) ⟨x, hx⟩ = 0 by simpa using hker) ⟨i, hi⟩
    have hle : (star x ⬝ᵥ A *ᵥ x).re ≤ 0 := by
      rw [re_star_dotProduct_mulVec_eq_sum hA x]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · simp [hzero i hi]
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    have hx0 : x = 0 := by
      by_contra hne
      exact absurd hle (not_le.mpr (hW x hx hne))
    exact Subtype.ext hx0
  have h1 : Module.finrank ℂ W
      ≤ Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) = posIndex hA := by
    rw [Module.finrank_pi, Fintype.card_subtype]
    rfl
  omega

end Zeta23Redux.LinAlg


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

