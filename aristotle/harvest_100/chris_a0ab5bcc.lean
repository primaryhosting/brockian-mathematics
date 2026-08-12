import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open Module Module.End LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- If `A` and `B` commute, then `B` maps each eigenspace of `A` into itself. -/
lemma mapsTo_eigenspace_of_commute {A B : E →ₗ[ℂ] E} (hAB : A ∘ₗ B = B ∘ₗ A) (mu : ℂ) :
    ∀ v ∈ eigenspace A mu, B v ∈ eigenspace A mu := by
  intro v hv
  rw [mem_eigenspace_iff] at hv ⊢
  have h1 : A (B v) = B (A v) := congrArg (fun f => f v) hAB
  rw [h1, hv, map_smul]

omit [FiniteDimensional ℂ E] in
/-- An eigenvalue of a symmetric operator is real (equal to the coercion of its real part). -/
lemma eigenvalue_eq_re {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) {mu : ℂ}
    (hmu : HasEigenvalue A mu) : ((mu.re : ℝ) : ℂ) = mu := by
  have h := hA.conj_eigenvalue_eq_self hmu
  have him : mu.im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  simp [Complex.ext_iff, him]

/-- **Two commuting Hermitian (self-adjoint) operators on a finite-dimensional complex inner
product space are simultaneously diagonalizable**: there is an orthonormal basis of the space
consisting of vectors that are simultaneously eigenvectors of both operators, with real
eigenvalues. -/
theorem commuting_simultaneous {A B : E →ₗ[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : A ∘ₗ B = B ∘ₗ A) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      (∀ i, ∃ a : ℝ, A (b i) = (a : ℂ) • b i) ∧
      (∀ i, ∃ c : ℝ, B (b i) = (c : ℂ) • b i) := by
  classical
  -- the eigenspaces of `A`
  set V : Eigenvalues A → Submodule ℂ E := fun mu => eigenspace A (mu : ℂ) with hV
  have hinv : ∀ mu : Eigenvalues A, ∀ v ∈ V mu, B v ∈ V mu := fun mu =>
    mapsTo_eigenspace_of_commute hAB (mu : ℂ)
  have hBres : ∀ mu : Eigenvalues A, (B.restrict (hinv mu)).IsSymmetric := fun mu =>
    hB.restrict_invariant (hinv mu)
  -- eigenbasis of `B` restricted to each eigenspace of `A`
  let bs : ∀ mu : Eigenvalues A, OrthonormalBasis (Fin (finrank ℂ (V mu))) ℂ (V mu) :=
    fun mu => (hBres mu).eigenvectorBasis rfl
  let b0 : OrthonormalBasis (Σ mu : Eigenvalues A, Fin (finrank ℂ (V mu))) ℂ E :=
    hA.direct_sum_isInternal.collectedOrthonormalBasis hA.orthogonalFamily_eigenspaces' bs
  have hb0 : ∀ a : Σ mu : Eigenvalues A, Fin (finrank ℂ (V mu)), b0 a = (bs a.1 a.2 : E) := by
    intro a
    simp [b0, DirectSum.IsInternal.collectedOrthonormalBasis]
    rfl
  have hcard : Fintype.card (Σ mu : Eigenvalues A, Fin (finrank ℂ (V mu))) = finrank ℂ E :=
    (finrank_eq_card_basis b0.toBasis).symm
  let e : (Σ mu : Eigenvalues A, Fin (finrank ℂ (V mu))) ≃ Fin (finrank ℂ E) :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨b0.reindex e, ?_, ?_⟩
  · intro i
    set a := e.symm i with ha
    refine ⟨(a.1 : ℂ).re, ?_⟩
    have hmem : b0 a ∈ V a.1 := by
      rw [hb0 a]; exact (bs a.1 a.2).2
    have : A (b0 a) = (a.1 : ℂ) • b0 a := mem_eigenspace_iff.mp hmem
    rw [OrthonormalBasis.reindex_apply, ← ha, this]
    rw [show (((a.1 : ℂ).re : ℝ) : ℂ) = (a.1 : ℂ) from eigenvalue_eq_re hA a.1.2]
  · intro i
    set a := e.symm i with ha
    refine ⟨(hBres a.1).eigenvalues rfl a.2, ?_⟩
    have hres : (B.restrict (hinv a.1)) (bs a.1 a.2)
        = (((hBres a.1).eigenvalues rfl a.2 : ℝ) : ℂ) • bs a.1 a.2 :=
      (hBres a.1).apply_eigenvectorBasis rfl a.2
    have hcoe : B ((bs a.1 a.2 : E))
        = (((hBres a.1).eigenvalues rfl a.2 : ℝ) : ℂ) • (bs a.1 a.2 : E) := by
      have := congrArg (fun x : V a.1 => (x : E)) hres
      simpa [LinearMap.restrict_apply] using this
    rw [OrthonormalBasis.reindex_apply, ← ha, hb0 a, hcoe]

end QPhys

-- Axiom check for the main result.
#print axioms QPhys.commuting_simultaneous

