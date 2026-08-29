import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Module.End Submodule

namespace QPhys

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A nonzero vector in the `μ`-eigenspace of a symmetric (Hermitian) operator witnesses that `μ`
is a genuine eigenvalue, and hence that `μ` is real. -/
lemma eigenvalue_eq_re_of_isSymmetric {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {μ : 𝕜} {x : E}
    (hx : x ≠ 0) (hxμ : A x = μ • x) : ((RCLike.re μ : ℝ) : 𝕜) = μ := by
  have hev : Module.End.HasEigenvalue A μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hxμ, hx⟩
  exact RCLike.conj_eq_iff_re.mp (hA.conj_eigenvalue_eq_self hev)

variable [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}

/-- The nontrivial joint eigenspaces of two operators on a finite-dimensional space are indexed by
a finite set of pairs of scalars. -/
lemma finite_nontrivial_jointEigenspace_index :
    Finite {p : 𝕜 × 𝕜 // (eigenspace A p.2 ⊓ eigenspace B p.1 : Submodule 𝕜 E) ≠ ⊥} := by
  have key : ∀ p : {p : 𝕜 × 𝕜 // (eigenspace A p.2 ⊓ eigenspace B p.1 : Submodule 𝕜 E) ≠ ⊥},
      Module.End.HasEigenvalue A p.1.2 ∧ Module.End.HasEigenvalue B p.1.1 := by
    rintro ⟨⟨b, a⟩, hp⟩
    constructor
    · rw [Module.End.hasEigenvalue_iff]
      intro h
      exact hp (by simp [h])
    · rw [Module.End.hasEigenvalue_iff]
      intro h
      exact hp (by simp [h])
  haveI : Finite {μ : 𝕜 // Module.End.HasEigenvalue A μ} :=
    (Module.End.finite_hasEigenvalue A).to_subtype
  haveI : Finite {μ : 𝕜 // Module.End.HasEigenvalue B μ} :=
    (Module.End.finite_hasEigenvalue B).to_subtype
  refine Finite.of_injective
    (fun p ↦ ((⟨p.1.2, (key p).1⟩ : {μ : 𝕜 // Module.End.HasEigenvalue A μ}),
      (⟨p.1.1, (key p).2⟩ : {μ : 𝕜 // Module.End.HasEigenvalue B μ}))) ?_
  rintro ⟨⟨b₁, a₁⟩, h₁⟩ ⟨⟨b₂, a₂⟩, h₂⟩ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  simp [h.1, h.2]

/-- **Commuting Hermitian operators are simultaneously diagonalizable.**

If `A` and `B` are commuting symmetric (self-adjoint, i.e. Hermitian) linear operators on a
finite-dimensional complex (or real) inner product space `E`, then `E` admits an orthonormal basis
consisting of vectors that are simultaneously eigenvectors of `A` and of `B`, with real
eigenvalues. -/
theorem commuting_simultaneous (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (a b : Fin (finrank 𝕜 E) → ℝ),
      ∀ i, A (v i) = ((a i : ℝ) : 𝕜) • v i ∧ B (v i) = ((b i : ℝ) : 𝕜) • v i := by
  classical
  set W : 𝕜 × 𝕜 → Submodule 𝕜 E := fun p ↦ eigenspace A p.2 ⊓ eigenspace B p.1 with hW
  have hfam₀ : OrthogonalFamily 𝕜 (fun p : 𝕜 × 𝕜 ↦ W p) fun p ↦ (W p).subtypeₗᵢ :=
    hA.orthogonalFamily_eigenspace_inf_eigenspace hB
  have htop : (⨆ p : 𝕜 × 𝕜, W p) = ⊤ :=
    (hA.directSum_isInternal_of_commute hB hAB).submodule_iSup_eq_top
  haveI : Finite {p : 𝕜 × 𝕜 // W p ≠ ⊥} := finite_nontrivial_jointEigenspace_index
  haveI : Fintype {p : 𝕜 × 𝕜 // W p ≠ ⊥} := Fintype.ofFinite _
  have hfam : OrthogonalFamily 𝕜 (fun p : {p : 𝕜 × 𝕜 // W p ≠ ⊥} ↦ W p.1)
      fun p ↦ (W p.1).subtypeₗᵢ := hfam₀.comp Subtype.val_injective
  have hint : DirectSum.IsInternal fun p : {p : 𝕜 × 𝕜 // W p ≠ ⊥} ↦ W p.1 := by
    refine hfam.isInternal_iff.mpr ?_
    rw [show (⨆ p : {p : 𝕜 × 𝕜 // W p ≠ ⊥}, W p.1) = ⨆ p : 𝕜 × 𝕜, W p from
      iSup_ne_bot_subtype W, htop, Submodule.top_orthogonal_eq_bot]
  set v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
    hint.subordinateOrthonormalBasis rfl hfam with hv
  have hmem : ∀ i, v i ∈ W (hint.subordinateOrthonormalBasisIndex rfl i hfam).1 := fun i ↦
    hint.subordinateOrthonormalBasis_subordinate rfl i hfam
  have hne : ∀ i, v i ≠ 0 := by
    intro i hi
    exact v.toBasis.ne_zero i (by simpa using hi)
  refine ⟨v, fun i ↦ RCLike.re (hint.subordinateOrthonormalBasisIndex rfl i hfam).1.2,
    fun i ↦ RCLike.re (hint.subordinateOrthonormalBasisIndex rfl i hfam).1.1, fun i ↦ ?_⟩
  obtain ⟨hA', hB'⟩ := hmem i
  have hA'' : A (v i) = (hint.subordinateOrthonormalBasisIndex rfl i hfam).1.2 • v i :=
    Module.End.mem_eigenspace_iff.mp hA'
  have hB'' : B (v i) = (hint.subordinateOrthonormalBasisIndex rfl i hfam).1.1 • v i :=
    Module.End.mem_eigenspace_iff.mp hB'
  exact ⟨by rw [eigenvalue_eq_re_of_isSymmetric hA (hne i) hA'']; exact hA'',
    by rw [eigenvalue_eq_re_of_isSymmetric hB (hne i) hB'']; exact hB''⟩

end QPhys

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

