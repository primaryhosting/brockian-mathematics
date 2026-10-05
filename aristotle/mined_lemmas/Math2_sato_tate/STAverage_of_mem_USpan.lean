/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma STAverage_of_mem_USpan {θ : ℕ → ℝ}
    (hmom : ∀ n : ℕ, 1 ≤ n → Tendsto (primeAvg θ (UBasis n)) atTop (𝓝 0))
    {g : ℝ → ℝ} (hg : g ∈ USpan) : STAverage θ g := by
  have key : ∀ h ∈ USpan, Continuous h ∧ STAverage θ h := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
        obtain ⟨k, rfl⟩ := hh
        exact ⟨continuous_UBasis k, STAverage_UBasis hmom k⟩
    | zero => exact ⟨continuous_const, STAverage_zero⟩
    | add h1 h2 _ _ ih1 ih2 =>
        exact ⟨ih1.1.add ih2.1, STAverage_add ih1.1 ih2.1 ih1.2 ih2.2⟩
    | smul c h _ ih => exact ⟨ih.1.const_smul c, STAverage_smul c ih.2⟩
  exact (key g hg).2

