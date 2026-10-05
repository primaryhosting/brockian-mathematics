/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

lemma finner_self_eq (f : ℕ →₀ ℂ) :
    finner f f = ((∑ i ∈ f.support, Complex.normSq (f i) : ℝ) : ℂ) := by
  rw [finner]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Complex.normSq_eq_conj_mul_self]

