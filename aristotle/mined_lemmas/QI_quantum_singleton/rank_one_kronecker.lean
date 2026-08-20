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

lemma rank_one_kronecker {K : ℕ} (ρ : Matrix X X ℂ) :
    ((1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ ρ).rank = K * ρ.rank := by
  have key : Submodule.map (LinearEquiv.curry ℂ ℂ (Fin K) X).toLinearMap
      (LinearMap.range ((1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ ρ).mulVecLin)
      = Submodule.pi Set.univ (fun _ : Fin K => LinearMap.range ρ.mulVecLin) := by
    apply le_antisymm
    · rintro w ⟨v, ⟨u, rfl⟩, rfl⟩
      intro i _
      refine ⟨fun y => u (i, y), ?_⟩
      funext x
      simp [LinearEquiv.curry, Matrix.mulVecLin, Matrix.mulVec, dotProduct, Matrix.kroneckerMap,
        Fintype.sum_prod_type, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
    · intro w hw
      choose u hu using fun i => hw i (Set.mem_univ i)
      refine ⟨_, ⟨fun p => u p.1 p.2, rfl⟩, ?_⟩
      funext i x
      have h2 := congrFun (hu i) x
      simp only [Matrix.mulVecLin_apply] at h2 ⊢
      simp [LinearEquiv.curry, Matrix.mulVec, dotProduct, Matrix.kroneckerMap,
        Fintype.sum_prod_type, Matrix.one_apply, ite_mul, Finset.sum_ite_eq] at h2 ⊢
      exact h2
  rw [Matrix.rank, ← (LinearEquiv.curry ℂ ℂ (Fin K) X).finrank_map_eq, key,
    finrank_pi_submodule, Fintype.card_fin, Matrix.rank]

/-- A nonzero matrix has rank at least one. -/
