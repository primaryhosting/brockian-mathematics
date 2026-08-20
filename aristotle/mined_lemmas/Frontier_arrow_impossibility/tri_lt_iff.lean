import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem tri_lt_iff (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x y : Fin 3) :
    (tri a b).lt x y ↔ ((x = a ∧ y ≠ a) ∨ (x = b ∧ y = c)) := by
  rw [tri, dif_pos (triR_inj a b hab), Ranking.ofRank_lt]
  revert hab hac hbc; revert a b c x y; decide

/-! ## Social welfare functions -/

section Defs

variable {α : Type u} {V : Type v}

/-- Weak Pareto / unanimity: a strict preference shared by all voters is the social
preference. -/
