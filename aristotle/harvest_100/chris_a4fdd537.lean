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

/-- The positive index of a Hermitian matrix: the number of strictly positive eigenvalues
(counted with multiplicity, i.e. the number of indices carrying a positive eigenvalue). -/
noncomputable def posIndex {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter (fun i : Fin d => 0 < hA.eigenvalues i)).card

/-- Diagonalization of the Hermitian quadratic form: if `A = U * diagonal L * star U`,
then `Re (star x ⬝ᵥ A *ᵥ x) = ∑ i, L i * ‖(star U *ᵥ x) i‖ ^ 2`. -/
theorem re_quadratic_form_of_spectral {d : ℕ} (A U : Matrix (Fin d) (Fin d) ℂ) (L : Fin d → ℝ)
    (hspec : A = U * diagonal (RCLike.ofReal ∘ L) * star U) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re = ∑ i, L i * ‖(star U *ᵥ x) i‖ ^ 2 := by
  set y : Fin d → ℂ := star U *ᵥ x with hy
  have key : star x ⬝ᵥ A *ᵥ x = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ L) *ᵥ y) := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
    congr 1
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  rw [key]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, Function.comp_apply,
    Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  norm_num
  ring

/-- **Sylvester's law of inertia** (Hermitian case, the "pull-back does not increase the
positive index" direction).  If `A` is a Hermitian complex `d × d` matrix and `W` is a
complex subspace of `Fin d → ℂ` on which the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is
positive definite, then `finrank W ≤ posIndex A`, the number of strictly positive
eigenvalues of `A`. -/
theorem sylvester_hermitian_finrank {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  set L : Fin d → ℝ := hA.eigenvalues with hLdef
  have hspec : A = U * diagonal (RCLike.ofReal ∘ L) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut] at h
    simp only [Unitary.toUnits, MonoidHom.coe_mk, OneHom.coe_mk] at h
    simpa [hUdef, hLdef] using h
  set S : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => 0 < L i) with hSdef
  -- the coordinate map onto the "positive" eigen-coordinates
  let f : W →ₗ[ℂ] ({i : Fin d // i ∈ S} → ℂ) :=
    { toFun := fun x i => (star U *ᵥ (x : Fin d → ℂ)) i.1
      map_add' := by
        intro x y
        funext i
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c x
        funext i
        simp [Matrix.mulVec_smul] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hx0 : (x : Fin d → ℂ) ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    have hpos := hW (x : Fin d → ℂ) x.2 hx0
    rw [re_quadratic_form_of_spectral A U L hspec] at hpos
    have hsum : ∑ i, L i * ‖(star U *ᵥ (x : Fin d → ℂ)) i‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos (fun i _ => ?_)
      by_cases hi : 0 < L i
      · have hzero : (star U *ᵥ (x : Fin d → ℂ)) i = 0 := by
          have : f x ⟨i, by simp [hSdef, hi]⟩ = 0 := by rw [hx]; rfl
          simpa [f] using this
        simp [hzero]
      · have hLi : L i ≤ 0 := le_of_not_gt hi
        have : (0:ℝ) ≤ ‖(star U *ᵥ (x : Fin d → ℂ)) i‖ ^ 2 := by positivity
        exact mul_nonpos_of_nonpos_of_nonneg hLi this
    linarith
  have h1 : Module.finrank ℂ W ≤ Module.finrank ℂ ({i : Fin d // i ∈ S} → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℂ ({i : Fin d // i ∈ S} → ℂ) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [h2] at h1
  simpa [posIndex, hSdef, hLdef] using h1

end Zeta23Redux.LinAlg

