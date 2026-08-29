/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required
-- header appears above as a plain comment and again below as a docstring.)

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

noncomputable section

/-! ## The quantum ingredients

We work with two qubits, i.e. with the space of functions `Fin 2 × Fin 2 → ℂ`,
equipped with the standard Hermitian inner product. -/

/-- The standard Hermitian inner product on the two-qubit space. -/

theorem pbrVec_orthonormal (k j : Fin 4) :
    inner4 (pbrVec k) (pbrVec j) = if k = j then 1 else 0 := by
  fin_cases k <;> fin_cases j <;>
    simp only [inner4_expand, pbrVec, Matrix.cons_val'] <;>
    norm_num [conj_rt, map_ofNat, rt_sq]

/-! ## Ontological models with preparation independence -/

/-- An ontological (hidden variable) model for the two preparations `|0⟩` and
`|+⟩` together with the PBR measurement on two independently prepared systems.

* `mu b` is the probability distribution over the ontic state space `Λ`
  associated with the preparation `prep b`;
* `resp k λ₁ λ₂` is the response function: the probability that the PBR
  measurement performed on the pair of systems with ontic states `λ₁, λ₂`
  yields outcome `k`;
* `born` expresses **preparation independence** (the ontic state of the pair
  is distributed as the product `mu b₁ ⊗ mu b₂`) together with the requirement
  that the model reproduce the quantum (Born rule) statistics. -/
structure OntologicalModel (Λ : Type*) [Fintype Λ] where
  mu : Bool → Λ → ℝ
  mu_nonneg : ∀ b l, 0 ≤ mu b l
  mu_sum_one : ∀ b, ∑ l, mu b l = 1
  resp : Fin 4 → Λ → Λ → ℝ
  resp_nonneg : ∀ k l₁ l₂, 0 ≤ resp k l₁ l₂
  resp_sum_one : ∀ l₁ l₂, ∑ k, resp k l₁ l₂ = 1
  born : ∀ (k : Fin 4) (b₁ b₂ : Bool),
    ∑ l₁, ∑ l₂, mu b₁ l₁ * mu b₂ l₂ * resp k l₁ l₂ = bornProb k b₁ b₂

variable {Λ : Type*} [Fintype Λ]

/-- In any such model, a response function vanishes at any ontic state that
lies in the support of both `mu false` and `mu true`. -/
