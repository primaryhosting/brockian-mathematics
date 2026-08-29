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
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

/-- The positive index of inertia of a Hermitian matrix `A`: the number of indices `i` at which
the eigenvalue `hA.eigenvalues i` is strictly positive (i.e. the number of strictly positive
eigenvalues of `A`, counted with multiplicity). -/
noncomputable def posIndex {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  Finset.card {i : Fin d | 0 < hA.eigenvalues i}

/-- Diagonalization of the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)`: in the coordinates
`y = U⋆ x` given by the eigenvector unitary `U` of `A`, the form is
`∑ i, eigenvalue i * ‖y i‖²`. -/
theorem hermitian_quadraticForm_eq_sum {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re
      = ∑ i, hA.eigenvalues i *
          Complex.normSq (((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) i) := by
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin d → ℝ, lam = hA.eigenvalues := ⟨_, rfl⟩
  rw [← hU, ← hlam]
  have hAeq : A = U * (Matrix.diagonal (RCLike.ofReal ∘ lam)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hlam]
  obtain ⟨y, hy⟩ : ∃ y : Fin d → ℂ, y = star U *ᵥ x := ⟨_, rfl⟩
  rw [← hy]
  have hstar : star x ᵥ* U = star y := by
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have key : star x ⬝ᵥ (A *ᵥ x)
      = star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ lam) *ᵥ y) := by
    rw [hAeq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hstar, ← hy]
  rw [key]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply,
    Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.normSq_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.ofReal_re]
  ring

/-- If all the coordinates of `x` along eigenvectors with a strictly positive eigenvalue vanish,
then the Hermitian form of `A` at `x` is nonpositive. -/
theorem hermitian_quadraticForm_nonpos_of_pos_coords_zero {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (x : Fin d → ℂ)
    (hx : ∀ i : Fin d, 0 < hA.eigenvalues i →
      ((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) i = 0) :
    (star x ⬝ᵥ (A *ᵥ x)).re ≤ 0 := by
  rw [hermitian_quadraticForm_eq_sum hA x]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hA.eigenvalues i) with h | h
  · simp [hx i h]
  · exact mul_nonpos_of_nonpos_of_nonneg h (Complex.normSq_nonneg _)

/-- **Sylvester's law of inertia** (Hermitian case, the inequality used in the paper).
If `A` is a Hermitian complex matrix and `W` is a complex subspace of `Fin d → ℂ` on which the
Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is positive definite, then `finrank W ≤ posIndex A`,
i.e. pulling back the form to `W` cannot increase the positive index of inertia. -/
theorem sylvester_hermitian_finrank {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  classical
  -- the coordinate map onto the positive-eigenvalue coordinates
  set S : Type := {i : Fin d // 0 < hA.eigenvalues i} with hS
  let f : W →ₗ[ℂ] (S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : S → Fin d)).comp
      ((Matrix.mulVecLin (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))).comp
        W.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun z hz => ?_
    have hz' : ∀ i : Fin d, 0 < hA.eigenvalues i →
        ((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ (z : Fin d → ℂ)) i = 0 := by
      intro i hi
      have := congrFun (LinearMap.mem_ker.1 hz) (⟨i, hi⟩ : S)
      simpa [f, LinearMap.funLeft_apply, Matrix.mulVecLin_apply] using this
    have hnonpos : (star (z : Fin d → ℂ) ⬝ᵥ (A *ᵥ (z : Fin d → ℂ))).re ≤ 0 :=
      hermitian_quadraticForm_nonpos_of_pos_coords_zero hA _ hz'
    by_contra hne
    have hzne : (z : Fin d → ℂ) ≠ 0 := by
      simpa [Submodule.coe_eq_zero] using hne
    exact absurd hnonpos (not_le.2 (hW (z : Fin d → ℂ) z.2 hzne))
  have hle : Module.finrank ℂ W ≤ Module.finrank ℂ (S → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hcard : Module.finrank ℂ (S → ℂ) = posIndex hA := by
    rw [Module.finrank_pi]
    simp [posIndex, hS, Fintype.card_subtype]
  exact hcard ▸ hle

end Zeta23Redux.LinAlg

#print axioms Zeta23Redux.LinAlg.sylvester_hermitian_finrank

