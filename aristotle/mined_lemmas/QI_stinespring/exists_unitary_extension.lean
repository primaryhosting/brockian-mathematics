/-
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Finite-dimensional Stinespring dilation theorem: every completely positive
trace-preserving (CPTP) linear map on matrix algebras can be realised by
adjoining an ancilla in a fixed pure state, applying a unitary on the enlarged
system, and tracing out the environment.

The main result is `QI.stinespring`. Along the way we prove Choi's theorem
(`QI.choi_posSemidef`), the Kraus decomposition of a completely positive map
(`QI.exists_kraus`), the completeness relation for the Kraus operators of a
trace-preserving map (`QI.kraus_sum_eq_one`), and the extension of an isometry
to a unitary (`QI.exists_unitary_extension`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {A B : Type*}

/-- The partial trace of a matrix on a bipartite system `B ⊗ E` over the second
(environment) factor. -/

lemma exists_unitary_extension {X Y Z : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (W : Matrix Y X ℂ) (hW : Wᴴ * W = 1) {f : X → Z} (hf : Function.Injective f)
    (hcard : Fintype.card Z = Fintype.card Y) :
    ∃ U : Matrix Y Z ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ (y : Y) (x : X), U y (f x) = W y x := by
  classical
  set col : X → EuclideanSpace ℂ Y := fun x => WithLp.toLp 2 (fun y => W y x) with hcol
  set v : Z → EuclideanSpace ℂ Y := Function.extend f col 0 with hv
  have hinner : ∀ x x' : X, (inner ℂ (col x) (col x') : ℂ) = if x = x' then 1 else 0 := by
    intro x x'
    have h1 : (inner ℂ (col x) (col x') : ℂ) = ∑ y, star (W y x) * W y x' := by
      simp [hcol, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have h2 := congrFun (congrFun hW x) x'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h2
    rw [h1, ← h2]
  have horth : Orthonormal ℂ (Set.restrict (Set.range f) v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨z, x, rfl⟩ ⟨z', x', rfl⟩
    simp only [Set.restrict_apply, hv, hf.extend_apply]
    rw [hinner]
    simp [hf.eq_iff, Subtype.ext_iff]
  have hrank : Module.finrank ℂ (EuclideanSpace ℂ Y) = Fintype.card Z := by
    simp [hcard]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hrank
  have hbo := orthonormal_iff_ite.mp b.orthonormal
  set U : Matrix Y Z ℂ := Matrix.of (fun y z => (b z).ofLp y) with hU
  have h1 : Uᴴ * U = 1 := by
    ext z z'
    have hz := hbo z z'
    rw [PiLp.inner_apply] at hz
    simp only [hU, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      RCLike.inner_apply] at hz ⊢
    rw [← hz]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : U * Uᴴ = 1 := by
    obtain ⟨g⟩ : Nonempty (Y ≃ Z) := ⟨Fintype.equivOfCardEq hcard.symm⟩
    have hV : (U.submatrix (Equiv.refl Y) g)ᴴ * (U.submatrix (Equiv.refl Y) g) = 1 := by
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h1,
        Matrix.submatrix_one_equiv]
    have hV2 := mul_eq_one_comm.mp hV
    ext y y'
    have hyy := congrFun (congrFun hV2 y) y'
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
      Equiv.refl_apply, Matrix.one_apply] at hyy ⊢
    rw [← hyy, ← Equiv.sum_comp g (fun z => U y z * star (U y' z))]
  refine ⟨U, h1, h2, ?_⟩
  intro y x
  have hbf := hb (f x) ⟨x, rfl⟩
  simp only [hU, Matrix.of_apply, hbf, hv, hf.extend_apply, hcol]

/-- Auxiliary form of the Stinespring dilation theorem: a map given by a Kraus
decomposition whose Kraus operators satisfy the completeness relation is a
unitary dilation. -/
