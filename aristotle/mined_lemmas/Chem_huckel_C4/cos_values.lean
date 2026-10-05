import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene,
with `α = 0`, `β = 1`): vertices are `Fin 4` arranged in a cycle, and `i ~ j` iff
`j = i + 1` or `i = j + 1` (addition modulo `4`). -/

theorem cos_values (μ : ℝ) :
    (∃ k : Fin 4, μ = 2 * Real.cos (2 * π * k / 4)) ↔ (μ = 2 ∨ μ = 0 ∨ μ = -2) := by
  have h0 : (2 : ℝ) * Real.cos (2 * π * ((0 : Fin 4) : ℕ) / 4) = 2 := by norm_num
  have h1 : (2 : ℝ) * Real.cos (2 * π * ((1 : Fin 4) : ℕ) / 4) = 0 := by
    have h : (2 : ℝ) * π * ((1 : Fin 4) : ℕ) / 4 = π / 2 := by norm_num; ring
    rw [h, Real.cos_pi_div_two, mul_zero]
  have h2 : (2 : ℝ) * Real.cos (2 * π * ((2 : Fin 4) : ℕ) / 4) = -2 := by
    have h : (2 : ℝ) * π * ((2 : Fin 4) : ℕ) / 4 = π := by norm_num; ring
    rw [h, Real.cos_pi]; norm_num
  have h3 : (2 : ℝ) * Real.cos (2 * π * ((3 : Fin 4) : ℕ) / 4) = 0 := by
    have h : (2 : ℝ) * π * ((3 : Fin 4) : ℕ) / 4 = π + π / 2 := by norm_num; ring
    rw [h, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi]
    ring
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h3)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
    · exact ⟨2, h2.symm⟩

/-- **Hückel theory for cyclobutadiene (`C₄`).**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₄`
(i.e. `C4adj *ᵥ v = μ • v` for some nonzero `v`) if and only if
`μ = 2 * cos (2 * π * k / 4)` for some `k ∈ {0, 1, 2, 3}`. -/
