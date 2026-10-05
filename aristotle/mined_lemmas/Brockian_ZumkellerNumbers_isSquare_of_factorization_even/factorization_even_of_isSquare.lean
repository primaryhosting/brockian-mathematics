import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset


lemma factorization_even_of_isSquare {t : ℕ} (h : IsSquare t) (p : ℕ) :
    Even (t.factorization p) := by
  obtain ⟨m, rfl⟩ := h
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [Nat.factorization_mul hm hm]
    exact ⟨_, rfl⟩

/-- A positive natural number has an odd number of divisors iff it is a square. -/
