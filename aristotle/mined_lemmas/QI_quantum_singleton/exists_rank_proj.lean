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

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

theorem exists_rank_proj {β X : Type*} [Fintype β] [DecidableEq β] [Fintype X] [DecidableEq X]
    (F : Matrix β X ℂ) :
    ∃ (P : Matrix β (Fin F.rank) ℂ) (R : Matrix (Fin F.rank) β ℂ), P * R * F = F := by
  classical
  have hfr : Module.finrank ℂ (LinearMap.range F.mulVecLin) = F.rank := rfl
  set W := LinearMap.range F.mulVecLin with hWdef
  let b : Basis (Fin F.rank) ℂ W := Module.finBasisOfFinrankEq ℂ _ hfr
  let P : Matrix β (Fin F.rank) ℂ := Matrix.of fun x s => ((b s : W) : β → ℂ) x
  have hPmul : ∀ v : Fin F.rank → ℂ, P.mulVec v = ∑ s, v s • ((b s : W) : β → ℂ) := by
    intro v; funext x
    simp [Matrix.mulVec, dotProduct, P, Finset.sum_apply, mul_comm]
  have hPinj : LinearMap.ker P.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.mulVecLin_apply, hPmul] at hv
    have h0 : ∑ s, v s • (b s) = 0 := by
      apply Subtype.ext
      push_cast [Submodule.coe_sum]
      simpa using hv
    funext s
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) v h0 s
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hPinj
  have hPtm : LinearMap.toMatrix' P.mulVecLin = P :=
    (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  refine ⟨P, LinearMap.toMatrix' g, ?_⟩
  have hRP : (LinearMap.toMatrix' g) * P = 1 := by
    have h := LinearMap.toMatrix'_comp g P.mulVecLin
    rw [hg, hPtm] at h
    simpa using h.symm
  have key : ∀ w ∈ W, (P * LinearMap.toMatrix' g).mulVec w = w := by
    intro w hw
    obtain ⟨c, hc⟩ : ∃ c : Fin F.rank → ℂ, P.mulVec c = w := by
      refine ⟨fun s => b.repr ⟨w, hw⟩ s, ?_⟩
      rw [hPmul]
      have h1 := congrArg (fun z : W => (z : β → ℂ)) (b.sum_repr ⟨w, hw⟩)
      push_cast [Submodule.coe_sum] at h1
      simpa using h1
    rw [← hc, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRP, Matrix.mul_one]
  ext x j
  have hcol : (fun y => F y j) ∈ W :=
    ⟨Pi.single j 1, by
      funext y
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']⟩
  have h2 := key _ hcol
  have hm : ((P * LinearMap.toMatrix' g) * F) x j
      = ((P * LinearMap.toMatrix' g).mulVec (fun y => F y j)) x := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hm, h2]

/-- Multilinear ("Tucker") rank inequality: the rank of a matrix whose rows are indexed by a
product `β × γ` is at most the product of the ranks of its two mode flattenings. -/
