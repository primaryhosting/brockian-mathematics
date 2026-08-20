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


theorem iia_pair {F : (V → Ranking α) → Ranking α} (hiia : IIA F) (P Q : V → Ranking α)
    (x y : α) (hxy : x ≠ y) (h : ∀ i, ((P i).lt x y ↔ (Q i).lt x y)) :
    ((F P).lt x y ↔ (F Q).lt x y) := by
  refine hiia P Q x y (fun i => ⟨h i, ?_⟩)
  rw [(P i).lt_iff_not_lt hxy, (Q i).lt_iff_not_lt hxy, h i]

end Defs

/-! ## A combinatorial pivot lemma -/

/-- If a membership-invariant predicate on coalitions fails for the empty coalition but
holds for some coalition, then there is a coalition `S` and a voter `i ∉ S` for which
adding `i` to `S` flips the predicate. -/
