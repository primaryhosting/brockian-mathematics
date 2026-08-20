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

theorem finitarySzemeredi_one : FinitarySzemeredi 1 := by
  intro δ hδ
  refine ⟨1, fun N hN S _ hcard => ?_⟩
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hcard
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
  refine ⟨a, 1, one_pos, fun i hi => ?_⟩
  interval_cases i
  simpa using ha

