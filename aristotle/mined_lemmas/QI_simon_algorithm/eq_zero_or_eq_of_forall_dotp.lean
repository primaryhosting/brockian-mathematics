import RequestProject.SimonQuantum

/-!
# Recovering the hidden shift from the measured samples

Each run of the quantum subroutine returns a uniformly random `y ∈ s^⊥`.  After `m`
runs the classical post-processing solves the linear system `t ⬝ y_i = 0` and outputs the
unique nonzero solution, which succeeds exactly when the samples *determine* `s`.
We bound the number of sample sequences that fail to determine `s`.
-/

open scoped BigOperators

namespace QI

variable {n : ℕ}

/-- The samples `y : Fin m → BV n` determine the hidden shift `s`: the only vectors
orthogonal to all of them are `0` and `s`. -/

lemma eq_zero_or_eq_of_forall_dotp {s t : BV n}
    (h : ∀ y : BV n, dotp s y = 0 → dotp t y = 0) : t = 0 ∨ t = s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ht0, hts⟩ := hcon
  -- find `y` with `dotp s y = 0` and `dotp t y = 1`
  obtain ⟨i, hi⟩ : ∃ i, t i = 1 := by
    by_contra hc
    push_neg at hc
    exact ht0 (funext fun i => by
      rcases QI.ZMod.two_cases (t i) with h0 | h1
      · simpa using h0
      · exact absurd h1 (hc i))
  by_cases hsi : s i = 0
  · exact absurd (h (e i) (by simpa using hsi)) (by simp [hi])
  · have hsi1 : s i = 1 := by
      rcases QI.ZMod.two_cases (s i) with h0 | h1
      · exact absurd h0 hsi
      · exact h1
    -- `t ≠ s`, so there is `j` with `t j ≠ s j`
    obtain ⟨j, hj⟩ : ∃ j, t j ≠ s j := by
      by_contra hc
      push_neg at hc
      exact hts (funext hc)
    have hji : j ≠ i := by
      rintro rfl; exact hj (by rw [hi, hsi1])
    rcases QI.ZMod.two_cases (s j) with hsj | hsj
    · -- s j = 0, t j = 1: use e j
      have htj : t j = 1 := by
        rcases QI.ZMod.two_cases (t j) with h0 | h1
        · exact absurd (by rw [h0, hsj]) hj
        · exact h1
      exact absurd (h (e j) (by simpa using hsj)) (by simp [htj])
    · -- s j = 1, t j = 0: use e i + e j
      have htj : t j = 0 := by
        rcases QI.ZMod.two_cases (t j) with h0 | h1
        · exact h0
        · exact absurd (by rw [h1, hsj]) hj
      have hzero : dotp s (e i + e j) = 0 := by
        rw [dotp_add_right, dotp_e, dotp_e, hsi1, hsj]; decide
      have := h _ hzero
      rw [dotp_add_right, dotp_e, dotp_e, hi, htj] at this
      simp at this

end QI

import Mathlib

/-!
# Simon's problem: basic definitions

`BV n` is the `n`-dimensional Boolean vector space `F_2^n`, `dotp` is the standard
bilinear form on it, and `IsSimon s f` says that `f` is a Simon function with hidden
shift `s`, i.e. `f x = f y ↔ y = x ∨ y = x + s` with `s ≠ 0`.
-/

open scoped BigOperators

namespace QI

/-- The `n`-dimensional Boolean vector space `F_2^n` (bit strings of length `n`). -/
abbrev BV (n : ℕ) : Type := Fin n → ZMod 2

/-- The standard bilinear (inner) product on `F_2^n`. -/
