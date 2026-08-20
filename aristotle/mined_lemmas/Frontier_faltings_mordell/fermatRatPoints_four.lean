/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/

theorem fermatRatPoints_four :
    fermatRatPoints 4 = {((1 : ℚ), (0 : ℚ)), (-1, 0), (0, 1), (0, -1)} := by
  have flt : FermatLastTheoremWith ℚ 4 := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour
  have hroot : ∀ t : ℚ, t ^ 4 = 1 → t = 1 ∨ t = -1 := by
    intro t ht
    have hfac : (t - 1) * (t + 1) * (t ^ 2 + 1) = 0 := by nlinarith [ht]
    have hpos : t ^ 2 + 1 ≠ 0 := by positivity
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · exact absurd h hpos
  ext ⟨x, y⟩
  simp only [fermatRatPoints, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · intro h
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      have : y ^ 4 = 1 := by linarith [h]
      rcases hroot y this with hy | hy
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hy⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, hy⟩))
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have : x ^ 4 = 1 := by linarith [h]
      rcases hroot x this with hx' | hx'
      · exact Or.inl ⟨hx', rfl⟩
      · exact Or.inr (Or.inl ⟨hx', rfl⟩)
    · exact absurd (by rw [h]; norm_num : x ^ 4 + y ^ 4 = (1 : ℚ) ^ 4)
        (flt x y 1 hx hy one_ne_zero)
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩) <;> subst hx <;> subst hy <;> norm_num

/-- The Fermat quartic, of genus `3`, has finitely many rational points. -/
