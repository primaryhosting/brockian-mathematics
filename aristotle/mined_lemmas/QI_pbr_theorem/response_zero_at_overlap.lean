/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

/-! ### Two-qubit vectors, inner products and the states involved -/

/-- A (pure) qubit state vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit state vector, written in curried form. -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- The product (tensor) of two qubit vectors. -/

private lemma response_zero_at_overlap {Λ : Type*} [Fintype Λ]
    {μ : Qubit → Λ → ℝ} {ξ : Fin 4 → Λ → Λ → ℝ} {k : Fin 4} {a b : Qubit} {l : Λ}
    (hμ : ∀ a l, 0 ≤ μ a l) (hξ : ∀ k l₁ l₂, 0 ≤ ξ k l₁ l₂)
    (h : ∑ l₁, ∑ l₂, μ a l₁ * μ b l₂ * ξ k l₁ l₂ = 0)
    (hp : 0 < μ a l) (hq : 0 < μ b l) : ξ k l l = 0 := by
  have hinner : ∀ l₁ ∈ Finset.univ, 0 ≤ ∑ l₂, μ a l₁ * μ b l₂ * ξ k l₁ l₂ := by
    intro l₁ _
    exact Finset.sum_nonneg fun l₂ _ =>
      mul_nonneg (mul_nonneg (hμ _ _) (hμ _ _)) (hξ _ _ _)
  have h1 : ∑ l₂, μ a l * μ b l₂ * ξ k l l₂ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hinner).1 h l (Finset.mem_univ l)
  have h2 : ∀ l₂ ∈ Finset.univ, 0 ≤ μ a l * μ b l₂ * ξ k l l₂ := fun l₂ _ =>
    mul_nonneg (mul_nonneg (hμ _ _) (hμ _ _)) (hξ _ _ _)
  have h3 : μ a l * μ b l * ξ k l l = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg h2).1 h1 l (Finset.mem_univ l)
  rcases mul_eq_zero.1 h3 with h4 | h4
  · rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 (ne_of_gt hp)
    · exact absurd h5 (ne_of_gt hq)
  · exact h4

/--
**The Pusey–Barrett–Rudolph theorem** (the ψ-ontic conclusion for the pair
`|0⟩`, `|+⟩`).

Setting: an ontological model assigns to each pure quantum state `a` a
probability density `μ a` over a (finite) space `Λ` of ontic states, and to a
measurement on two systems a response function `ξ k l₁ l₂` giving the
probability of outcome `k` when the ontic states of the two systems are
`l₁, l₂` (so `∑ k, ξ k l₁ l₂ = 1`).

*Preparation independence* is the hypothesis `hborn`: when the two systems are
prepared independently in `a` and `b`, the joint ontic distribution is the
product `μ a ⊗ μ b`, and the model reproduces the quantum (Born) predictions
for the PBR measurement.

Conclusion: the distributions of the distinct, non-orthogonal states `|0⟩` and
`|+⟩` have disjoint supports; no ontic state is compatible with both. Hence the
quantum state cannot be merely epistemic: it is ontic.

Normalisation of the `μ a` is not needed for the argument, so it is not assumed.
-/
