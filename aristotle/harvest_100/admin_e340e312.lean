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

/-- The Hermitian form attached to a matrix `A`: `x ↦ Re (star x ⬝ᵥ (A *ᵥ x))`. -/
noncomputable def hermForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity).  For a non-Hermitian matrix the value is `0`. -/
noncomputable def posIndex {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℕ :=
  if hA : A.IsHermitian then Fintype.card {i : Fin d // 0 < hA.eigenvalues i} else 0

lemma posIndex_eq {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    posIndex A = Fintype.card {i : Fin d // 0 < hA.eigenvalues i} := dif_pos hA

section

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)

/-- The unitary change of coordinates diagonalizing `A`. -/
noncomputable def diagCoord (x : Fin d → ℂ) : Fin d → ℂ :=
  (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x

/-- In the eigenbasis coordinates the Hermitian form is a weighted sum of squared moduli. -/
lemma hermForm_eq_sum (x : Fin d → ℂ) :
    hermForm A x = ∑ i, hA.eigenvalues i * Complex.normSq (diagCoord hA x i) := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  have hAeq : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, mul_assoc] using this
  have hmul : A *ᵥ x = U *ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (star U *ᵥ x)) := by
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M *ᵥ x) hAeq
    simpa only [← Matrix.mulVec_mulVec] using h
  have hstar : star x ᵥ* U = star (star U *ᵥ x) := by
    have : star ((Uᴴ) *ᵥ x) = star x ᵥ* (Uᴴ)ᴴ := Matrix.star_mulVec _ _
    simpa using this.symm
  have key : star x ⬝ᵥ (A *ᵥ x)
      = star (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (star U *ᵥ x)) := by
    rw [hmul, Matrix.dotProduct_mulVec, hstar]
  have : star x ⬝ᵥ (A *ᵥ x)
      = ∑ i, ((hA.eigenvalues i : ℂ) * (Complex.normSq (diagCoord hA x i) : ℂ)) := by
    rw [key]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def,
      Function.comp_apply, diagCoord, hU]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [hermForm, this]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

/-- The linear map sending a vector to its eigen-coordinates in the positive eigenspaces. -/
noncomputable def posCoord (W : Submodule ℂ (Fin d → ℂ)) :
    W →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) where
  toFun x := fun i => diagCoord hA (x : Fin d → ℂ) i
  map_add' x y := by
    funext i
    simp [diagCoord, Matrix.mulVec_add]
  map_smul' c x := by
    funext i
    simp [diagCoord, Matrix.mulVec_smul]

end

/-- **Sylvester's law of inertia** (Hermitian form, the inequality used in the paper).
If the Hermitian form of a Hermitian matrix `A` is positive definite on a complex subspace `W`
of `Fin d → ℂ`, then `finrank W ≤ posIndex A`, the number of strictly positive eigenvalues
of `A`. -/
theorem sylvester_hermitian_finrank {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hpos : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re) :
    Module.finrank ℂ W ≤ posIndex A := by
  classical
  have hinj : Function.Injective (posCoord hA W) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have hx0 : ∀ i : Fin d, 0 < hA.eigenvalues i → diagCoord hA (x : Fin d → ℂ) i = 0 := by
      intro i hi
      have := congrFun (LinearMap.mem_ker.1 hx) ⟨i, hi⟩
      simpa [posCoord] using this
    have hle : hermForm A (x : Fin d → ℂ) ≤ 0 := by
      rw [hermForm_eq_sum hA]
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hi | hi
      · simp [hx0 i hi]
      · exact mul_nonpos_of_nonpos_of_nonneg hi (Complex.normSq_nonneg _)
    by_contra hne
    have hxne : (x : Fin d → ℂ) ≠ 0 := by
      intro h
      exact hne (Subtype.ext h)
    exact absurd (hpos (x : Fin d → ℂ) x.2 hxne) (not_lt.2 hle)
  have := LinearMap.finrank_le_finrank_of_injective (f := posCoord hA W) hinj
  rw [posIndex_eq hA]
  simpa [Module.finrank_pi] using this

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

