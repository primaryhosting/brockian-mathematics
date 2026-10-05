/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory

namespace Frontier

/-- Pointwise CHSH inequality: for outcomes in `[-1, 1]`, the CHSH combination is
bounded by `2`. -/

theorem chsh_pointwise (a₁ a₂ b₁ b₂ : ℝ)
    (ha₁ : |a₁| ≤ 1) (ha₂ : |a₂| ≤ 1) (hb₁ : |b₁| ≤ 1) (hb₂ : |b₂| ≤ 1) :
    |a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂| ≤ 2 := by
  have h1 : |a₁ * (b₁ + b₂)| ≤ |b₁ + b₂| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (b₁ + b₂)]
  have h2 : |a₂ * (b₁ - b₂)| ≤ |b₁ - b₂| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (b₁ - b₂)]
  have h3 : |b₁ + b₂| + |b₁ - b₂| ≤ 2 := by
    rcases abs_cases (b₁ + b₂) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (b₁ - b₂) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rw [abs_le] at hb₁ hb₂ <;> rw [e1, e2] <;> linarith [hb₁.1, hb₁.2, hb₂.1, hb₂.2]
  have key : a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂ = a₁ * (b₁ + b₂) + a₂ * (b₁ - b₂) := by ring
  rw [key]
  calc |a₁ * (b₁ + b₂) + a₂ * (b₁ - b₂)| ≤ |a₁ * (b₁ + b₂)| + |a₂ * (b₁ - b₂)| := abs_add_le _ _
    _ ≤ 2 := by linarith

/-- A local hidden-variable model: a probability space of hidden variables `Ω` together with
deterministic (`[-1,1]`-valued) response functions for two measurement settings on each side. -/
structure LHVModel (Ω : Type) [MeasurableSpace Ω] where
  /-- The distribution of the hidden variable. -/
  μ : Measure Ω
  /-- The hidden variable distribution is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- Alice's response function for setting `1`. -/
  A₁ : Ω → ℝ
  /-- Alice's response function for setting `2`. -/
  A₂ : Ω → ℝ
  /-- Bob's response function for setting `1`. -/
  B₁ : Ω → ℝ
  /-- Bob's response function for setting `2`. -/
  B₂ : Ω → ℝ
  hA₁ : ∀ ω, |A₁ ω| ≤ 1
  hA₂ : ∀ ω, |A₂ ω| ≤ 1
  hB₁ : ∀ ω, |B₁ ω| ≤ 1
  hB₂ : ∀ ω, |B₂ ω| ≤ 1
  intAB : ∀ i j : Fin 2, Integrable
    (fun ω => (if i = 0 then A₁ ω else A₂ ω) * (if j = 0 then B₁ ω else B₂ ω)) μ

namespace LHVModel

variable {Ω : Type} [MeasurableSpace Ω]

/-- The correlation predicted by the model for settings `(i, j)`. -/
