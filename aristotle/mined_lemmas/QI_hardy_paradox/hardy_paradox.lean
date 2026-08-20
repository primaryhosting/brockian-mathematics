import Mathlib
/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory

namespace QI

/-- **Hardy's paradox, deterministic (local hidden variable) form.**

In a local realistic model, each hidden variable `l : Λ` deterministically fixes the outcomes
`a 1 l, a 2 l` of Alice's two possible measurement settings and `b 1 l, b 2 l` of Bob's.
The four Hardy conditions

* some run has `a₁ = b₁ = 1` (this is the positive-probability event),
* never `a₁ = 1` and `b₂ = 1`,
* never `a₂ = 1` and `b₁ = 1`,
* always `a₂ = 1` or `b₂ = 1`,

are jointly contradictory: no local hidden variable assignment can reproduce them. -/

theorem hardy_paradox {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A₁ A₂ B₁ B₂ : Set Ω)
    (h₁ : μ (A₁ ∩ B₂) = 0)
    (h₂ : μ (A₂ ∩ B₁) = 0)
    (h₃ : μ (A₂ᶜ ∩ B₂ᶜ) = 0) :
    μ (A₁ ∩ B₁) = 0 := by
  have hsub : A₁ ∩ B₁ ⊆ (A₁ ∩ B₂) ∪ (A₂ ∩ B₁) ∪ (A₂ᶜ ∩ B₂ᶜ) := by
    rintro x ⟨hx1, hx2⟩
    by_cases hA₂ : x ∈ A₂
    · exact Or.inl (Or.inr ⟨hA₂, hx2⟩)
    · by_cases hB₂ : x ∈ B₂
      · exact Or.inl (Or.inl ⟨hx1, hB₂⟩)
      · exact Or.inr ⟨hA₂, hB₂⟩
  refine measure_mono_null hsub ?_
  simp [measure_union_null_iff, h₁, h₂, h₃]

/-- **Hardy's paradox, contradiction form.**

If in addition a strictly positive fraction of the runs exhibits the event `A₁ ∩ B₁`
(as quantum mechanics predicts), the local realistic description is outright contradictory. -/
