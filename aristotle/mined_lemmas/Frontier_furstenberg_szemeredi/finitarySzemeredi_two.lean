/- (Lean requires `import` to precede any module docstring, so the header below is a
plain block comment; it is repeated verbatim as a module docstring after the import.)
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

noncomputable section

open Classical in
/-- The number of elements of `A` below `N`. -/

theorem finitarySzemeredi_two : FinitarySzemeredi 2 := by
  intro δ hδ
  refine ⟨⌈2 / δ⌉₊, fun N hN S _ hcard => ?_⟩
  have h1 : (2:ℝ) / δ ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have h2 : (2:ℝ) ≤ δ * N := by
    rw [div_le_iff₀ hδ] at h1; linarith
  have hcard2 : (2:ℝ) ≤ (S.card : ℝ) := le_trans h2 hcard
  have hlt : 1 < S.card := by exact_mod_cast (by exact_mod_cast hcard2 : (2:ℕ) ≤ S.card)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using ha
    · have hb' : a + 1 * (b - a) = b := by omega
      rw [hb']; exact hb
  · refine ⟨b, a - b, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hb
    · have ha' : b + 1 * (a - b) = a := by omega
      rw [ha']; exact ha

/-- Longer progressions give shorter ones: the finitary statement is antitone in `k`. -/
