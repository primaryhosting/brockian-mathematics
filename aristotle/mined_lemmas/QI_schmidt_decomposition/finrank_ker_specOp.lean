import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Finset Matrix

variable {m n : ℕ}

/-- `IsSchmidtDecomp psi s e f` says that the bipartite pure state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, written as its coordinate array) has the Schmidt decomposition
`psi = ∑ k, s k • (e k ⊗ f k)`, where the Schmidt coefficients `s k` are strictly positive
and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomp {ι : Type} [Fintype ι] (psi : Fin m → Fin n → ℂ)
    (s : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m)) (f : ι → EuclideanSpace ℂ (Fin n)) :
    Prop where
  coeff_pos : ∀ k, 0 < s k
  orthonormal_left : Orthonormal ℂ e
  orthonormal_right : Orthonormal ℂ f
  decomp : ∀ i j, psi i j = ∑ k, (s k : ℂ) * e k i * f k j

/-- The self-adjoint operator `∑ k, c k • ⟪e k, ·⟫ • e k`. -/

lemma finrank_ker_specOp {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (e : ι → EuclideanSpace ℂ (Fin m)) (he : Orthonormal ℂ e) (t : ℝ) (ht : t ≠ 0) :
    Module.finrank ℂ
        (LinearMap.ker (specOp c e - (t : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] _)))
      = (univ.filter (fun k => c k = t)).card := by
  classical
  have hij : ∀ j k, (inner ℂ (e j) (e k) : ℂ) = if j = k then 1 else 0 :=
    orthonormal_iff_ite.mp he
  have hTe : ∀ (j : ι) (v : EuclideanSpace ℂ (Fin m)),
      (inner ℂ (e j) (specOp c e v) : ℂ) = (c j : ℂ) * inner ℂ (e j) v := by
    intro j v
    rw [specOp_apply, inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right, inner_smul_right, hij j j, if_pos rfl]; ring
    · intro l _ hl
      rw [inner_smul_right, inner_smul_right, hij j l, if_neg (Ne.symm hl)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  have hker : LinearMap.ker
        (specOp c e - (t : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] _))
      = Submodule.span ℂ (Set.range (e ∘ (Subtype.val : {k : ι // c k = t} → ι))) := by
    apply le_antisymm
    · intro v hv
      have hv' : specOp c e v = (t : ℂ) • v := by
        have h := LinearMap.mem_ker.mp hv
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          sub_eq_zero] at h
        exact h
      have hzero : ∀ j, c j ≠ t → (inner ℂ (e j) v : ℂ) = 0 := by
        intro j hj
        have h1 : (c j : ℂ) * inner ℂ (e j) v = (t : ℂ) * inner ℂ (e j) v := by
          rw [← hTe j v, hv', inner_smul_right]
        have h2 : ((c j : ℂ) - t) * inner ℂ (e j) v = 0 := by linear_combination h1
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd (by exact_mod_cast sub_eq_zero.mp h) hj
        · exact h
      have hrep : v = (t : ℂ)⁻¹ • ∑ k, (c k : ℂ) • ((inner ℂ (e k) v : ℂ) • e k) := by
        rw [← specOp_apply, hv', smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht), one_smul]
      rw [hrep]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => ?_)
      by_cases hk : c k = t
      · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
      · rw [hzero k hk]; simp
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero, Function.comp_apply]
      rw [specOp_apply, Finset.sum_eq_single k.1]
      · rw [hij k.1 k.1, if_pos rfl, smul_smul, mul_one, k.2]
      · intro l _ hl; rw [hij l k.1, if_neg hl]; simp
      · intro h; exact absurd (Finset.mem_univ k.1) h
  rw [hker, finrank_span_eq_card (he.comp _ Subtype.val_injective).linearIndependent,
    Fintype.card_subtype]

/-- Two families of strictly positive coefficients defining the same operator agree
as multisets. -/
