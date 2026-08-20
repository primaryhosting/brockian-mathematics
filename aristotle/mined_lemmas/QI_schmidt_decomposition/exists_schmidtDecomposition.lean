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

theorem exists_schmidtDecomposition (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
      (v : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi σ u v := by
  classical
  have hA : (reducedLeft psi).IsHermitian := reducedLeft_isHermitian psi
  set w := hA.eigenvectorBasis with hwdef
  set lam := hA.eigenvalues with hlamdef
  have hw : ∀ k, (reducedLeft psi) *ᵥ (w k).ofLp = lam k • (w k).ofLp :=
    fun k => hA.mulVec_eigenvectorBasis k
  set y : Fin m → EuclideanSpace ℂ (Fin n) := fun k => yvec psi (fun i => w i) k with hydef
  have hyy : ∀ k l, ⟪y k, y l⟫_ℂ = (lam k : ℂ) * (if l = k then 1 else 0) :=
    inner_yvec psi w lam hw
  have hself : ∀ k, ⟪y k, y k⟫_ℂ = (lam k : ℂ) := by
    intro k
    rw [hyy k k, if_pos rfl, mul_one]
  have hnn : ∀ k, 0 ≤ lam k := by
    intro k
    have h2 := inner_self_nonneg (𝕜 := ℂ) (x := y k)
    rw [hself k] at h2
    simpa using h2
  have hzero : ∀ k, lam k = 0 → y k = 0 := by
    intro k hk
    have h := hself k
    rw [hk] at h
    exact inner_self_eq_zero (𝕜 := ℂ) (x := y k) |>.mp (by simpa using h)
  set s : Finset (Fin m) := Finset.univ.filter (fun k => lam k ≠ 0) with hsdef
  set e : Fin s.card → Fin m := fun t => ((s.equivFin.symm t : {x // x ∈ s}) : Fin m) with hedef
  have hemem : ∀ t, e t ∈ s := fun t => (s.equivFin.symm t).2
  have hepos : ∀ t, 0 < lam (e t) := by
    intro t
    have h := hemem t
    rw [hsdef, Finset.mem_filter] at h
    exact lt_of_le_of_ne (hnn _) (Ne.symm h.2)
  have heinj : Function.Injective e :=
    Subtype.val_injective.comp s.equivFin.symm.injective
  have hsq : ∀ t, ((Real.sqrt (lam (e t)) : ℝ) : ℂ) ≠ 0 := by
    intro t
    simpa using (Real.sqrt_pos.mpr (hepos t)).ne'
  refine ⟨s.card, fun t => Real.sqrt (lam (e t)), fun t => w (e t),
    fun t => ((Real.sqrt (lam (e t)) : ℝ) : ℂ)⁻¹ • y (e t), ?_, ?_, ?_, ?_⟩
  · intro t; exact Real.sqrt_pos.mpr (hepos t)
  · exact w.orthonormal.comp e heinj
  · rw [orthonormal_iff_ite]
    intro t l
    rw [inner_smul_left, inner_smul_right, hyy]
    rcases eq_or_ne t l with rfl | htl
    · have h1 : ((Real.sqrt (lam (e t)) : ℝ) : ℂ) * ((Real.sqrt (lam (e t)) : ℝ) : ℂ)
          = (lam (e t) : ℂ) := by
        norm_cast
        exact Real.mul_self_sqrt (le_of_lt (hepos t))
      have hne := hsq t
      rw [if_pos rfl, map_inv₀, Complex.conj_ofReal, mul_one, if_pos rfl, ← h1]
      field_simp
    · rw [if_neg (fun h => htl (heinj h).symm), if_neg htl]
      ring
  · intro i j
    have h1 : psi (i, j) = ∑ k, w k i * y k j := coeff_eq_sum_yvec psi w i j
    have h2 : ∑ k, w k i * y k j = ∑ k ∈ s, w k i * y k j := by
      refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
      intro k _ hk
      have hk0 : lam k = 0 := by
        rw [hsdef, Finset.mem_filter] at hk
        by_contra hne
        exact hk ⟨Finset.mem_univ k, hne⟩
      rw [hzero k hk0]
      simp
    have h3 : ∑ k ∈ s, w k i * y k j = ∑ t : Fin s.card, w (e t) i * y (e t) j := by
      rw [← Finset.sum_coe_sort s (fun k => w k i * y k j)]
      exact (Equiv.sum_comp s.equivFin.symm (fun x : {x // x ∈ s} => w x i * y x j)).symm
    rw [h1, h2, h3]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [PiLp.smul_apply, smul_eq_mul]
    field_simp [hsq t]

section Uniqueness

variable {ι : Type} [Fintype ι] {psi : EuclideanSpace ℂ (Fin m × Fin n)} {σ : ι → ℝ}
  {u : ι → EuclideanSpace ℂ (Fin m)} {v : ι → EuclideanSpace ℂ (Fin n)}

/-- The reduced density matrix computed from a Schmidt decomposition. -/
