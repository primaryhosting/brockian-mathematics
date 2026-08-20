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

theorem fermatRatPoints_finite_of_dvd {m n : ℕ} (hmn : m ∣ n)
    (h : (fermatRatPoints m).Finite) : (fermatRatPoints n).Finite := by
  obtain ⟨k, rfl⟩ := hmn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : fermatRatPoints (m * 0) = ∅ := by
      ext p
      simp [fermatRatPoints]
    rw [this]
    exact Set.finite_empty
  refine finite_of_finite_image_of_finite_fibers
    (f := fun p : ℚ × ℚ => (p.1 ^ k, p.2 ^ k)) ?_ ?_
  · refine h.subset ?_
    rintro q ⟨p, hp, rfl⟩
    simp only [fermatRatPoints, Set.mem_setOf_eq] at hp ⊢
    rw [← pow_mul, ← pow_mul, mul_comm k m]
    exact hp
  · rintro ⟨b1, b2⟩
    refine Set.Finite.subset
      (Set.Finite.prod (finite_setOf_pow_eq hk b1) (finite_setOf_pow_eq hk b2)) ?_
    rintro ⟨x, y⟩ hxy
    simp only [Set.mem_setOf_eq, Prod.mk.injEq] at hxy
    exact ⟨hxy.1, hxy.2⟩

/-- **Base case.**  The rational points of the genus-3 Fermat quartic `x ^ 4 + y ^ 4 = 1`
are exactly the four trivial ones.  This is a consequence of Fermat's Last Theorem for
exponent `4`. -/
