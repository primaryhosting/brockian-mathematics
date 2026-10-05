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

lemma finner_definite (f : ℕ →₀ ℂ) (h : finner f f = 0) : f = 0 := by
  rw [finner_self_eq] at h
  have hsum : ∑ i ∈ f.support, Complex.normSq (f i) = 0 := by exact_mod_cast h
  have hzero : ∀ i ∈ f.support, Complex.normSq (f i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).mp hsum
  ext i
  by_cases hi : i ∈ f.support
  · simpa using Complex.normSq_eq_zero.mp (hzero i hi)
  · simpa using Finsupp.notMem_support_iff.mp hi

/-- The Fock inner product, as an `Inner` structure. -/
