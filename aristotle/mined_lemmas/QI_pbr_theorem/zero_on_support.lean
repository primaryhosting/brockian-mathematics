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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-! ## The quantum ingredients

We work with two qubits, i.e. with `ℂ⁴` indexed by `Fin 4`, where the index `2*a + b`
stands for the product basis vector `|a⟩ ⊗ |b⟩`.
-/

/-- The inner product on `ℂ⁴` (conjugate-linear in the first argument). -/

lemma zero_on_support (M : OntologicalModel Λ) (a b : Fin 2) (i : Fin 4)
    (h : Complex.normSq (ip (xi i) (phi a b)) = 0) (l₁ l₂ : Λ)
    (h₁ : 0 < M.mu a l₁) (h₂ : 0 < M.mu b l₂) : M.P l₁ l₂ i = 0 := by
  have hsum := M.born a b i
  rw [h] at hsum
  have hnn : ∀ x ∈ (univ : Finset Λ), 0 ≤ ∑ y, M.mu a x * M.mu b y * M.P x y i := by
    intro x _
    exact sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (M.mu_nonneg a x) (M.mu_nonneg b y)) (M.P_nonneg x y i)
  have h1 : ∑ y, M.mu a l₁ * M.mu b y * M.P l₁ y i = 0 :=
    (sum_eq_zero_iff_of_nonneg hnn).mp hsum l₁ (mem_univ l₁)
  have hnn2 : ∀ y ∈ (univ : Finset Λ), 0 ≤ M.mu a l₁ * M.mu b y * M.P l₁ y i := fun y _ =>
    mul_nonneg (mul_nonneg (M.mu_nonneg a l₁) (M.mu_nonneg b y)) (M.P_nonneg l₁ y i)
  have h2 : M.mu a l₁ * M.mu b l₂ * M.P l₁ l₂ i = 0 :=
    (sum_eq_zero_iff_of_nonneg hnn2).mp h1 l₂ (mem_univ l₂)
  have := mul_pos h₁ h₂
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' (ne_of_gt this)
  · exact h'

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model that reproduces the
quantum predictions for the PBR measurement on two independently prepared systems
(preparation independence), the distributions over ontic states associated with the two
distinct pure states `|0⟩` and `|+⟩` have disjoint supports: no ontic state is compatible
with both preparations.  In other words, the quantum state is *ontic*, not merely
epistemic. -/
