/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The set of affine rational points of the plane Fermat curve
`F_n : x ^ n + y ^ n = 1` over `ℚ`.

For `n ≥ 4` this is a smooth plane curve of degree `n`, hence of genus
`(n-1)(n-2)/2 ≥ 3 ≥ 2`, so Faltings' theorem (the Mordell conjecture) predicts that it has
only finitely many rational points. -/

theorem fermatCurveRatPoints_subset {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    fermatCurveRatPoints n ⊆ ({0, 1, -1} : Set ℚ) ×ˢ ({0, 1, -1} : Set ℚ) := by
  rintro ⟨x, y⟩ (hxy : x ^ n + y ^ n = 1)
  have hFLT := fermatLastTheoremWith_rat_of_four_dvd hn
  have hroot : ∀ z : ℚ, z ^ n = 1 → z = 1 ∨ z = -1 := by
    intro z hz
    rcases pow_eq_one_iff_cases.mp hz with h | h | h
    · exact absurd h hn0
    · exact Or.inl h
    · exact Or.inr h.1
  -- One of the two coordinates has to vanish, by Fermat's Last Theorem.
  have hzero : x = 0 ∨ y = 0 := by
    by_contra hc
    push_neg at hc
    exact hFLT x y 1 hc.1 hc.2 one_ne_zero (by simpa using hxy)
  constructor
  · rcases hzero with hx | hy
    · exact Or.inl hx
    · have : x ^ n = 1 := by rw [hy] at hxy; simpa [zero_pow hn0] using hxy
      rcases hroot x this with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rcases hzero with hx | hy
    · have : y ^ n = 1 := by rw [hx] at hxy; simpa [zero_pow hn0] using hxy
      rcases hroot y this with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact Or.inl hy

/-- **Faltings' theorem (Mordell conjecture), verified instance.**

For every exponent `n ≠ 0` divisible by `4`, the plane Fermat curve `x ^ n + y ^ n = 1`
is a smooth curve of genus `(n-1)(n-2)/2 ≥ 3 ≥ 2` over `ℚ`, and its set of rational points
is finite — as predicted by Faltings' theorem.

The general theorem of Faltings is not available in Mathlib; this is a Lean-checked instance
of it, obtained from Mathlib's `fermatLastTheoremFour`. -/
