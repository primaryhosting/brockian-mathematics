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

lemma finrank_pi_submodule {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (p : Submodule ℂ M) [FiniteDimensional ℂ p] :
    finrank ℂ (Submodule.pi (Set.univ : Set ι) (fun _ => p)) = Fintype.card ι * finrank ℂ p := by
  have e : (Submodule.pi (Set.univ : Set ι) (fun _ : ι => p)) ≃ₗ[ℂ] (ι → p) :=
    { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl
      invFun := fun w => ⟨fun i => (w i : M), fun i _ => (w i).2⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }
  rw [e.finrank_eq, finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq X] in
/-- The rank of `1 ⊗ ρ` is `K * rank ρ`. -/
