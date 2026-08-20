import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

lemma continuous_modelV (g : ℕ) (s : Multiset ℝ) : Continuous fun L => modelV g (L ::ₘ s) := by
  by_cases h1 : g = 0 ∧ Multiset.card s + 1 = 3
  · have he : (fun L : ℝ => modelV g (L ::ₘ s)) = fun _ => 1 := by
      funext L; simp [modelV, Multiset.card_cons, h1.1, h1.2]
    rw [he]; exact continuous_const
  · by_cases h2 : g = 0 ∧ Multiset.card s + 1 = 4
    · have he : (fun L : ℝ => modelV g (L ::ₘ s))
          = fun L => 2 * π ^ 2 + (L ^ 2 + sqSum s) / 2 := by
        funext L
        simp only [modelV, Multiset.card_cons, sqSum_cons]
        rw [if_neg (by simpa [Multiset.card_cons] using h1), if_pos ⟨h2.1, h2.2⟩]
      rw [he]; fun_prop
    · by_cases h3 : g = 1 ∧ Multiset.card s + 1 = 1
      · have he : (fun L : ℝ => modelV g (L ::ₘ s))
            = fun L => ((L ^ 2 + sqSum s) + 4 * π ^ 2) / 24 := by
          funext L
          simp only [modelV, Multiset.card_cons, sqSum_cons]
          rw [if_neg (by simpa using h1), if_neg (by simpa using h2), if_pos ⟨h3.1, h3.2⟩]
        rw [he]; fun_prop
      · have he : (fun L : ℝ => modelV g (L ::ₘ s)) = fun _ => 0 := by
          funext L
          simp only [modelV, Multiset.card_cons, sqSum_cons]
          rw [if_neg (by simpa using h1), if_neg (by simpa using h2), if_neg (by simpa using h3)]
        rw [he]; exact continuous_const

/-- The hypotheses used in the four-holed sphere reduction are consistent: `modelV` satisfies the
continuity requirement, the two base cases, and every `g = 0`, `n = 4` instance of Mirzakhani's
recursion, and its four-holed sphere volume is `2π² + ½ Σ Lᵢ²`. -/
