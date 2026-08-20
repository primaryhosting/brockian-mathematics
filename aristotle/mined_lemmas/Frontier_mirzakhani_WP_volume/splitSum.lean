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

noncomputable def splitSum (V : ℕ → Multiset ℝ → ℝ) (g : ℕ) (rest : Multiset ℝ) (x y : ℝ) : ℝ :=
  ∑ g₁ ∈ Finset.range (g + 1),
    (rest.powerset.map fun I =>
      if 3 ≤ 2 * g₁ + (Multiset.card I + 1) ∧
          3 ≤ 2 * (g - g₁) + (Multiset.card (rest - I) + 1) then
        V g₁ (x ::ₘ I) * V (g - g₁) (y ::ₘ (rest - I))
      else 0).sum

/-- The `A^dcon` term of Mirzakhani's recursion: the contribution of the surfaces obtained by
removing a pair of pants that meets the distinguished boundary in one boundary circle and whose
two other boundary circles are glued to a *disconnected* surface. -/
