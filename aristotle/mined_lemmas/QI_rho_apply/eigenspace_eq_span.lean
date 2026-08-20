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

namespace QI

open Finset Matrix ComplexConjugate

variable {m n : ℕ}

/-- The coefficient matrix of a bipartite vector `ψ ∈ ℂ^m ⊗ ℂ^n`, where the tensor product is
modelled as `EuclideanSpace ℂ (Fin m × Fin n)`. -/

lemma eigenspace_eq_span {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) {t : ℝ} (ht : t ≠ 0) :
    Module.End.eigenspace (Matrix.toEuclideanLin (rho ψ)) (t : ℂ) =
      Submodule.span ℂ (Set.range (fun k : {k : Fin r // σ k ^ 2 = t} => e (k : Fin r))) := by
  have he : Orthonormal ℂ e := h.2.1
  have hip : ∀ (l k : Fin r), (inner ℂ (e l) (e k) : ℂ) = if l = k then 1 else 0 :=
    orthonormal_iff_ite.mp he
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff, toEuclideanLin_rho_of_decomp h v] at hv
    set c : Fin r → ℂ := fun k => inner ℂ (e k) v with hc
    have hkey : ∀ l : Fin r, ((σ l ^ 2 : ℝ) : ℂ) * c l = (t : ℂ) * c l := by
      intro l
      have h1 := congrArg (fun w => (inner ℂ (e l) w : ℂ)) hv
      simp only [inner_sum, inner_smul_right, hip, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
      simpa [hc] using h1
    have hzero : ∀ l : Fin r, σ l ^ 2 ≠ t → c l = 0 := by
      intro l hl
      have h1 := hkey l
      have h2 : (((σ l ^ 2 : ℝ) : ℂ) - (t : ℂ)) * c l = 0 := by ring_nf; linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h3) hl
      · exact h3
    have hsum : (t : ℂ) • v =
        (t : ℂ) • ∑ k ∈ Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t), c k • e k := by
      rw [← hv, Finset.smul_sum]
      rw [← Finset.sum_filter_of_ne (p := fun k : Fin r => σ k ^ 2 = t)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_filter] at hk
        rw [hk.2, smul_smul]
      · intro k _ hk
        by_contra hne
        exact hk (by
          rw [show (inner ℂ (e k) v : ℂ) = 0 from hzero k hne, mul_zero, zero_smul])
    have hv' : v = ∑ k ∈ Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t), c k • e k :=
      smul_right_injective _ htC hsum
    rw [hv']
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
    rw [Finset.mem_filter] at hk
    exact Submodule.subset_span ⟨⟨k, hk.2⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, toEuclideanLin_rho_of_decomp h]
    simp only [hip, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro l _ hl
      simp [hl]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'

