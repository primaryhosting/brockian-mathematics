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

theorem fermatRatPoints_three :
    fermatRatPoints 3 = {((1 : ℚ), (0 : ℚ)), (0, 1)} := by
  have flt : FermatLastTheoremWith ℚ 3 := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree
  have hroot : ∀ t : ℚ, t ^ 3 = 1 → t = 1 := by
    intro t ht
    have hfac : (t - 1) * (t ^ 2 + t + 1) = 0 := by nlinarith [ht]
    have hpos : t ^ 2 + t + 1 ≠ 0 := by nlinarith [sq_nonneg (2 * t + 1)]
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exact absurd h hpos
  ext ⟨x, y⟩
  simp only [fermatRatPoints, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · intro h
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      have hy : y ^ 3 = 1 := by linarith [h]
      exact Or.inr ⟨rfl, hroot y hy⟩
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have hx' : x ^ 3 = 1 := by linarith [h]
      exact Or.inl ⟨hroot x hx', rfl⟩
    · exact absurd (by rw [h]; norm_num : x ^ 3 + y ^ 3 = (1 : ℚ) ^ 3)
        (flt x y 1 hx hy one_ne_zero)
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> subst hx <;> subst hy <;> norm_num

/-- The Fermat cubic has finitely many rational points. -/
