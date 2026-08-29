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

lemma finner_smul_left (r : ℂ) (f g : ℕ →₀ ℂ) :
    finner (r • f) g = (starRingEnd ℂ) r * finner f g := by
  classical
  have h1 : (r • f).support ⊆ f.support := Finsupp.support_smul
  rw [finner_eq_sum _ _ h1, finner, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [mul_assoc]

