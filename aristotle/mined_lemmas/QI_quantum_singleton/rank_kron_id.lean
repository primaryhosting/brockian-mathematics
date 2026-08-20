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

theorem rank_kron_id {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (σ : Matrix α α ℂ) :
    (Matrix.of fun p q : α × κ => σ p.1 q.1 * (if p.2 = q.2 then 1 else 0)).rank
      = Fintype.card κ * σ.rank := by
  classical
  set f : Matrix (α × κ) (α × κ) ℂ :=
    Matrix.of fun p q => σ p.1 q.1 * (if p.2 = q.2 then 1 else 0) with hf
  set E := curryEquiv α κ with hE
  have hcomm : (E : ((α × κ) → ℂ) →ₗ[ℂ] _) ∘ₗ f.mulVecLin
      = (σ.mulVecLin.compLeft κ) ∘ₗ (E : ((α × κ) → ℂ) →ₗ[ℂ] _) := by
    ext x i a
    simp [E, curryEquiv, Matrix.mulVec, dotProduct, f, LinearMap.compLeft,
      Fintype.sum_prod_type]
  have hmap : Submodule.map (E : ((α × κ) → ℂ) →ₗ[ℂ] _) (LinearMap.range f.mulVecLin)
      = LinearMap.range (σ.mulVecLin.compLeft κ) := by
    rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp]
    simp [LinearEquiv.range]
  have h1 : f.rank = finrank ℂ (LinearMap.range (σ.mulVecLin.compLeft κ)) := by
    rw [← hmap, Matrix.rank]
    exact (Submodule.equivMapOfInjective _ (E.injective) _).finrank_eq
  rw [h1, LinearMap.range_compLeft, (piSubEquiv (κ := κ) (LinearMap.range σ.mulVecLin)).finrank_eq,
    Module.finrank_pi_fintype]
  simp [Matrix.rank]

/-- A nonzero matrix has positive rank. -/
