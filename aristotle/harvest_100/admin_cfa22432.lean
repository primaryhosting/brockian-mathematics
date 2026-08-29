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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity, i.e. as a cardinality of the index set). -/
noncomputable def posIndex {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- Diagonalization of the Hermitian quadratic form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` in the
eigenvector coordinates `c = Uᴴ *ᵥ x`, where `U` is the eigenvector unitary of `A`. -/
lemma quadraticForm_eq_sum_eigenvalues {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re
      = ∑ i, hA.eigenvalues i *
          ‖((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *ᵥ x) i‖ ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set c := Uᴴ *ᵥ x with hc
  have hAeq : A = U * (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Uᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  conv_lhs => rw [hAeq, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  have h1 : star x ᵥ* U = star c := by
    rw [hc, star_mulVec, conjTranspose_conjTranspose]
  rw [h1]
  have h2 : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin d) (Fin d) ℂ) *ᵥ c
      = fun i => (hA.eigenvalues i : ℂ) * c i := by
    funext i; simp [mulVec_diagonal]
  rw [h2]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, mul_comm (starRingEnd ℂ (c i)), mul_assoc, Complex.conj_mul']
  norm_cast

/-- **Sylvester's law of inertia** (Hermitian case, the direction used in the paper):
if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is positive definite on a complex subspace
`W ≤ (Fin d → ℂ)`, then `finrank W` is at most the number of strictly positive eigenvalues
of `A`. -/
theorem sylvester_hermitian_finrank {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  -- the map sending `x ∈ W` to its coordinates along the positive eigenvectors
  let T : W →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) :=
    { toFun := fun x i => (Uᴴ *ᵥ (x : Fin d → ℂ)) i.1
      map_add' := by intro x y; funext i; simp [mulVec_add]
      map_smul' := by intro a x; funext i; simp [mulVec_smul] }
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : ∀ i : Fin d, 0 < hA.eigenvalues i → (Uᴴ *ᵥ (x : Fin d → ℂ)) i = 0 := by
      intro i hi
      have : T x = 0 := hx
      exact congrFun this ⟨i, hi⟩
    by_contra hne
    have hxne : (x : Fin d → ℂ) ≠ 0 := by
      simpa [Submodule.coe_eq_zero] using hne
    have hpos := hW (x : Fin d → ℂ) x.2 hxne
    rw [quadraticForm_eq_sum_eigenvalues hA] at hpos
    have hle : ∑ i, hA.eigenvalues i * ‖(Uᴴ *ᵥ (x : Fin d → ℂ)) i‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · rw [hx0 i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
    exact absurd hpos (not_lt.mpr hle)
  have h1 : Module.finrank ℂ W ≤ Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) :=
    T.finrank_le_finrank_of_injective hTinj
  have h2 : Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) = posIndex hA := by
    rw [Module.finrank_fintype_fun_eq_card, posIndex, Fintype.card_subtype]
  omega

end Zeta23Redux.LinAlg

