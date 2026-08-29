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

lemma resp_eq_zero_of_mem_overlap (M : OntologicalModel Λ) (l : Λ)
    (h0 : 0 < M.mu false l) (h1 : 0 < M.mu true l) (k : Fin 4) :
    M.resp k l l = 0 := by
  set b₁ := (excluded k).1 with hb₁
  set b₂ := (excluded k).2 with hb₂
  have hsum : ∑ l₁, ∑ l₂, M.mu b₁ l₁ * M.mu b₂ l₂ * M.resp k l₁ l₂ = 0 := by
    rw [M.born k b₁ b₂, hb₁, hb₂, bornProb_excluded k]
  have hnonneg : ∀ l₁ ∈ (Finset.univ : Finset Λ), (0:ℝ) ≤
      ∑ l₂, M.mu b₁ l₁ * M.mu b₂ l₂ * M.resp k l₁ l₂ := by
    intro l₁ _
    exact Finset.sum_nonneg fun l₂ _ =>
      mul_nonneg (mul_nonneg (M.mu_nonneg _ _) (M.mu_nonneg _ _)) (M.resp_nonneg _ _ _)
  have h1' : ∑ l₂, M.mu b₁ l * M.mu b₂ l₂ * M.resp k l l₂ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum l (Finset.mem_univ l)
  have hnonneg2 : ∀ l₂ ∈ (Finset.univ : Finset Λ), (0:ℝ) ≤
      M.mu b₁ l * M.mu b₂ l₂ * M.resp k l l₂ := fun l₂ _ =>
    mul_nonneg (mul_nonneg (M.mu_nonneg _ _) (M.mu_nonneg _ _)) (M.resp_nonneg _ _ _)
  have hterm : M.mu b₁ l * M.mu b₂ l * M.resp k l l = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg2).1 h1' l (Finset.mem_univ l)
  have hpos₁ : 0 < M.mu b₁ l := by cases b₁ <;> assumption
  have hpos₂ : 0 < M.mu b₂ l := by cases b₂ <;> assumption
  have := mul_ne_zero (ne_of_gt hpos₁) (ne_of_gt hpos₂)
  exact by
    rcases mul_eq_zero.1 hterm with h | h
    · exact absurd h this
    · exact h

/-- **Pusey–Barrett–Rudolph theorem.**  In any ontological model of quantum
theory satisfying preparation independence, the quantum state is *ontic*: the
ontic-state distributions of two distinct pure states (here `|0⟩` and `|+⟩`)
have disjoint supports, so the quantum state is a function of the ontic state
and cannot be merely a state of knowledge about it. -/
