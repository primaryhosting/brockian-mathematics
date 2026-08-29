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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The (finite) set of indices at which a Hermitian matrix has a strictly positive
eigenvalue. -/
noncomputable def posSet (hA : A.IsHermitian) : Finset (Fin d) :=
  Finset.univ.filter fun i => 0 < hA.eigenvalues i

/-- The positive index of inertia of a Hermitian matrix: the number of its strictly positive
eigenvalues (counted with multiplicity). -/
noncomputable def posIndex (hA : A.IsHermitian) : ℕ := (posSet hA).card

/-- Diagonalization of the Hermitian form: in the coordinates
`y = U* x` given by the unitary matrix `U` of eigenvectors, the Hermitian form
`x ↦ Re (star x ⬝ᵥ A *ᵥ x)` becomes `∑ i, λ i * ‖y i‖ ^ 2`. -/
theorem hermitian_form_eq_sum (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      ∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set y := star U *ᵥ x with hy
  have key : star x ⬝ᵥ (A *ᵥ x) = ∑ i, ((hA.eigenvalues i : ℂ) * ((‖y i‖ ^ 2 : ℝ) : ℂ)) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    have h1 : star x ᵥ* U = star y := by
      rw [hy, star_mulVec]
      simp [Matrix.star_eq_conjTranspose]
    rw [h1, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy]
    have h2 : star (y i) * y i = ((‖y i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']
      norm_cast
    simp only [Matrix.mulVec_diagonal, Function.comp_apply, Complex.coe_algebraMap]
    rw [show star y i * ((hA.eigenvalues i : ℂ) * y i)
        = (hA.eigenvalues i : ℂ) * (star (y i) * y i) by simp [Pi.star_apply]; ring, h2]
  rw [key]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Sylvester's law of inertia** (Hermitian version, the direction used in the paper).
If the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` of a Hermitian matrix `A` is positive
definite on a complex subspace `W ≤ (Fin d → ℂ)`, then `finrank W ≤ posIndex A`, the number
of strictly positive eigenvalues of `A`. -/
theorem sylvester_hermitian_finrank (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set S : Finset (Fin d) := posSet hA with hS
  -- the linear map sending `x` to the coordinates of `U* x` at positive eigenvalue indices
  set f : (Fin d → ℂ) →ₗ[ℂ] ({i // i ∈ S} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {i // i ∈ S} → Fin d)).comp
      (Matrix.mulVecLin (star U)) with hf
  set g : W →ₗ[ℂ] ({i // i ∈ S} → ℂ) := f.comp W.subtype with hg
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    have hx0 : (v : Fin d → ℂ) ≠ 0 := by
      simpa [Submodule.coe_eq_zero] using hv0
    have hpos := hW (v : Fin d → ℂ) v.2 hx0
    rw [hermitian_form_eq_sum hA] at hpos
    have hzero : ∀ i ∈ S, (star U *ᵥ (v : Fin d → ℂ)) i = 0 := by
      intro i hi
      have := congrFun hv ⟨i, hi⟩
      simpa [hg, hf, LinearMap.funLeft_apply, Matrix.mulVecLin_apply] using this
    have hle : ∑ i, hA.eigenvalues i * ‖(star U *ᵥ (v : Fin d → ℂ)) i‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : i ∈ S
      · rw [hzero i hi]
        simp
      · have hlam : hA.eigenvalues i ≤ 0 := by
          by_contra hlam
          exact hi (by simp [hS, posSet, Finset.mem_filter, not_le.mp (by simpa using hlam)])
        exact mul_nonpos_of_nonpos_of_nonneg hlam (by positivity)
    exact absurd hpos (not_lt.mpr (by simpa [hU] using hle))
  have hrank : Module.finrank ℂ W ≤ Module.finrank ℂ ({i // i ∈ S} → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_pi, Fintype.card_coe, posIndex, hS] using hrank

end Zeta23Redux.LinAlg

