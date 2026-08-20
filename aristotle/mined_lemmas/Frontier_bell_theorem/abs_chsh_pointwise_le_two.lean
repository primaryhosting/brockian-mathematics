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

open scoped Real
open MeasureTheory Matrix

namespace Frontier

/-! ## The classical (local hidden variable) side -/

/-- The pointwise CHSH bound: if four numbers `a₀, a₁, b₀, b₁` have absolute value at most `1`
(the possible outcomes, or local averages of outcomes, of `±1`-valued measurements), then the
CHSH combination is bounded by `2` in absolute value. -/

theorem abs_chsh_pointwise_le_two {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1)
    (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    |a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁| ≤ 2 := by
  rw [abs_le] at ha₀ ha₁ hb₀ hb₁ ⊢
  constructor <;>
  · rcases le_total 0 (b₀ + b₁) with hp | hp <;> rcases le_total 0 (b₀ - b₁) with hq | hq <;>
      nlinarith [ha₀.1, ha₀.2, ha₁.1, ha₁.2, hb₀.1, hb₀.2, hb₁.1, hb₁.2]

/-- A **local hidden variable model** for a bipartite experiment with two binary measurement
settings per side: a probability space of hidden variables `Ω`, together with response functions
`a i ω` (Alice, setting `i`) and `b j ω` (Bob, setting `j`) taking values in `[-1, 1]`.  The
crucial locality assumption is built into the shape of the data: Alice's response depends only on
her own setting `i` and on the shared hidden variable `ω` (and likewise for Bob). -/
structure LHVModel where
  /-- The space of hidden variables. -/
  Ω : Type
  /-- Measurable structure on the hidden variable space. -/
  measurable : MeasurableSpace Ω
  /-- The distribution of the hidden variable. -/
  μ : Measure Ω
  /-- The hidden variable is distributed according to a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- Alice's local response function for each of her two settings. -/
  a : Fin 2 → Ω → ℝ
  /-- Bob's local response function for each of his two settings. -/
  b : Fin 2 → Ω → ℝ
  /-- Alice's responses take values in `[-1, 1]`. -/
  ha : ∀ i ω, |a i ω| ≤ 1
  /-- Bob's responses take values in `[-1, 1]`. -/
  hb : ∀ j ω, |b j ω| ≤ 1
  /-- The correlation functions are integrable. -/
  hint : ∀ i j, Integrable (fun ω => a i ω * b j ω) μ

attribute [instance] LHVModel.measurable LHVModel.prob

/-- The correlation predicted by a local hidden variable model for settings `(i, j)`. -/
