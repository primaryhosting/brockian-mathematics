import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
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

open Finset Matrix
open scoped ComplexConjugate InnerProductSpace

namespace QI

variable {m n : ℕ}

/-- `IsSchmidtDecomposition psi σ u v` says that the bipartite pure state `psi`, a vector of the
tensor product `ℂ^m ⊗ ℂ^n` realized as `EuclideanSpace ℂ (Fin m × Fin n)`, is written as
`psi = ∑ k, σ k • (u k ⊗ v k)` where the `σ k` are strictly positive reals (the Schmidt
coefficients) and `u`, `v` are orthonormal families in the two factors. -/
structure IsSchmidtDecomposition {ι : Type} [Fintype ι]
    (psi : EuclideanSpace ℂ (Fin m × Fin n)) (σ : ι → ℝ)
    (u : ι → EuclideanSpace ℂ (Fin m)) (v : ι → EuclideanSpace ℂ (Fin n)) : Prop where
  coeff_pos : ∀ k, 0 < σ k
  left_orthonormal : Orthonormal ℂ u
  right_orthonormal : Orthonormal ℂ v
  sum_eq : ∀ i j, psi (i, j) = ∑ k, (σ k : ℂ) * u k i * v k j

/-- The matrix of coefficients of a bipartite state in the product basis. -/

lemma finrank_eigenspace_of_spectral {c : ι → ℝ}
    (hu : Orthonormal ℂ u) (T : Module.End ℂ (EuclideanSpace ℂ (Fin m)))
    (hT : ∀ x, T x = ∑ k, ((c k : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k)) {t : ℝ} (ht : 0 < t) :
    Module.finrank ℂ (T.eigenspace ((t : ℝ) : ℂ)) = #{k | c k = t} := by
  classical
  have htne : ((t : ℝ) : ℂ) ≠ 0 := by simpa using ht.ne'
  have hTinner : ∀ (l : ι) (x : EuclideanSpace ℂ (Fin m)),
      ⟪u l, T x⟫_ℂ = (c l : ℂ) * ⟪u l, x⟫_ℂ := by
    intro l x
    rw [hT x, inner_sum, Finset.sum_eq_single l]
    · rw [inner_smul_right, inner_smul_right, orthonormal_iff_ite.mp hu l l, if_pos rfl]
      ring
    · intro b _ hb
      rw [inner_smul_right, inner_smul_right, orthonormal_iff_ite.mp hu l b, if_neg (Ne.symm hb)]
      ring
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  have key : T.eigenspace ((t : ℝ) : ℂ)
      = Submodule.span ℂ (Set.range (fun k : {k : ι // c k = t} => u (k : ι))) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      have ha : ∀ l, c l ≠ t → ⟪u l, x⟫_ℂ = 0 := by
        intro l hl
        have h1 := hTinner l x
        rw [hx, inner_smul_right] at h1
        have h2 : ((c l : ℂ) - ((t : ℝ) : ℂ)) * ⟪u l, x⟫_ℂ = 0 := by linear_combination -h1
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (Complex.ofReal_inj.mp (sub_eq_zero.mp h3)) hl
        · exact h3
      have h1 : x = ((t : ℝ) : ℂ)⁻¹ • ∑ k, ((c k : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) := by
        rw [← hT x, hx, smul_smul, inv_mul_cancel₀ htne, one_smul]
      rw [Finset.smul_sum] at h1
      have h2 : (∑ k, ((t : ℝ) : ℂ)⁻¹ • (((c k : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k)))
          = ∑ k ∈ Finset.univ.filter (fun k => c k = t), ⟪u k, x⟫_ℂ • u k := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : c k = t
        · rw [if_pos hk, hk, smul_smul, inv_mul_cancel₀ htne, one_smul]
        · rw [if_neg hk, ha k hk, zero_smul, smul_zero, smul_zero]
      rw [h1.trans h2]
      refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨⟨k, (Finset.mem_filter.mp hk).2⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hT, Finset.sum_eq_single (k : ι)]
      · rw [orthonormal_iff_ite.mp hu (k : ι) (k : ι), if_pos rfl, k.2, one_smul]
      · intro b _ hb
        rw [orthonormal_iff_ite.mp hu b (k : ι), if_neg hb, zero_smul, smul_zero]
      · intro hk
        exact absurd (Finset.mem_univ (k : ι)) hk
  have hli : LinearIndependent ℂ (fun k : {k : ι // c k = t} => u (k : ι)) :=
    (hu.comp _ Subtype.val_injective).linearIndependent
  rw [key, finrank_span_eq_card hli]
  simp [Fintype.card_subtype]

end Uniqueness

/-- **Uniqueness** of the Schmidt coefficients: any two Schmidt decompositions of the same state
have the same number of terms and the same multiset of Schmidt coefficients. -/
