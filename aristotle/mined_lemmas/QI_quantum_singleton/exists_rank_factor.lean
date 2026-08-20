/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Kronecker ComplexOrder
open Matrix Module

namespace QI

section LinearAlgebra

variable {X W : Type*} [Fintype X] [Fintype W] [DecidableEq X] [DecidableEq W]

/-- Rank factorization: every matrix `F` factors as `U * L * F = F` with `U` having
`F.rank` columns. -/

lemma exists_rank_factor (F : Matrix X W ℂ) :
    ∃ (U : Matrix X (Fin F.rank) ℂ) (L : Matrix (Fin F.rank) X ℂ), U * L * F = F := by
  classical
  set V := LinearMap.range F.mulVecLin with hVdef
  have hfin : finrank ℂ V = F.rank := rfl
  let bs : Basis (Fin F.rank) ℂ V := Module.finBasisOfFinrankEq ℂ V hfin
  choose g hg using fun s : Fin F.rank => LinearMap.exists_extend (bs.coord s)
  refine ⟨Matrix.of fun x s => (bs s : X → ℂ) x, Matrix.of fun s x => g s (Pi.single x 1), ?_⟩
  have hgv : ∀ (s : Fin F.rank) (v : X → ℂ), ∑ x', g s (Pi.single x' 1) * v x' = g s v := by
    intro s v
    have step : ∀ x' : X, g s (Pi.single x' 1) * v x' = g s (Pi.single x' (v x')) := by
      intro x'
      have hs : (Pi.single x' (v x') : X → ℂ) = v x' • (Pi.single x' 1 : X → ℂ) := by
        funext y; by_cases h : y = x' <;> simp [Pi.single_apply, h]
      rw [hs, map_smul, smul_eq_mul, mul_comm]
    simp_rw [step]
    rw [← map_sum, Finset.univ_sum_single]
  have hkey : ∀ v : X → ℂ, v ∈ V → ∀ x, ∑ s, (bs s : X → ℂ) x * g s v = v x := by
    intro v hv x
    have h1 : ∀ s, g s v = bs.repr ⟨v, hv⟩ s := by
      intro s
      have := congrArg (fun (m : V →ₗ[ℂ] ℂ) => m ⟨v, hv⟩) (hg s)
      simpa [Basis.coord_apply] using this
    have h3 := congrArg (fun (w : V) => (w : X → ℂ) x) (bs.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h3
    simp_rw [h1]
    rw [← h3]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  ext x w
  have hmem : (fun x' => F x' w) ∈ V := by
    refine ⟨Pi.single w 1, ?_⟩
    funext x'
    simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  calc ∑ s, (bs s : X → ℂ) x * ∑ x', g s (Pi.single x' 1) * F x' w
      = ∑ s, (bs s : X → ℂ) x * g s (fun x' => F x' w) :=
        Finset.sum_congr rfl fun s _ => by rw [hgv s fun x' => F x' w]
    _ = F x w := hkey _ hmem x

/-- Rank subadditivity for tensor flattenings: the rank of the `(X × Y) | Z` flattening of a
three-index array is at most the product of the ranks of the `X | (Y × Z)` and `Y | (X × Z)`
flattenings. -/
