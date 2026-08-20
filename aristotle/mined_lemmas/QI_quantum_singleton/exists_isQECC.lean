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

theorem exists_isQECC : ∃ ψ : Fin (q ^ n) → ((Fin n → Fin q) → ℂ), IsQECC n q 1 (q ^ n) ψ := by
  classical
  have hcard : Fintype.card (Fin n → Fin q) = q ^ n := by simp
  set e : Fin (q ^ n) ≃ (Fin n → Fin q) := (Fintype.equivFinOfCardEq hcard).symm with he
  have key : ∀ i j : Fin (q ^ n), ∑ v : Fin n → Fin q,
      (if v = e i then (1 : ℂ) else 0) * (starRingEnd ℂ) (if v = e j then 1 else 0)
        = if i = j then 1 else 0 := by
    intro i j
    simp [apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq', e.injective.eq_iff, eq_comm]
  refine ⟨fun i v => if v = e i then 1 else 0, key, ?_⟩
  intro S hS
  have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
  subst hS0
  refine ⟨fun _ _ => 1, ?_⟩
  intro i j x y
  have hm : ∀ (x : {i // i ∈ (∅ : Finset (Fin n))} → Fin q)
      (z : {i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q),
      merge ∅ x z = emptyEquiv z := by
    intro x z; funext i; simp [merge, emptyEquiv]
  simp only [hm, mul_one]
  rw [Equiv.sum_comp emptyEquiv
    (fun v => (if v = e i then (1 : ℂ) else 0) * (starRingEnd ℂ) (if v = e j then 1 else 0))]
  exact key i j

/-- Glue configurations on `A`, on `B` and on the rest into a global configuration. -/
