/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Arrow's impossibility theorem

For a finite electorate `ι` and a set of alternatives `A` containing at least three elements,
there is no social welfare function `F : (ι → Pref A) → Pref A` that is simultaneously
unanimous (Pareto efficient), independent of irrelevant alternatives (IIA), and
non-dictatorial.

Individual and social preferences are modelled as strict linear orders (`Pref`), i.e.
transitive, irreflexive and total relations, `P.gt x y` meaning "`x` is strictly preferred
to `y`".

The proof is the classical "decisive coalition" argument:

* a coalition `S` is *weakly decisive* for the ordered pair `(x, y)` if whenever the members of
  `S` prefer `x` to `y` and everybody else prefers `y` to `x`, society prefers `x` to `y`;
* a coalition `S` is *decisive* if whenever all of its members prefer `x` to `y`, so does
  society;
* (field expansion) weak decisiveness for a single pair implies full decisiveness;
* (group contraction) if a decisive coalition splits into two disjoint pieces, one of the pieces
  is decisive;
* the whole electorate is decisive and the empty coalition is not, so by induction along a list
  enumerating the electorate some singleton coalition `{i}` is decisive — and `i` is then a
  dictator.

This file is deliberately self-contained: it depends on nothing but the Lean 4 core library.
-/

universe u v

namespace Frontier

/-- A strict preference relation on `A`: a transitive, irreflexive and total relation.
`P.gt x y` means "`x` is strictly preferred to `y`". -/
structure Pref (A : Type v) where
  /-- `gt x y` means that `x` is strictly preferred to `y`. -/
  gt : A → A → Prop
  /-- Preference is transitive. -/
  gt_trans : ∀ {x y z}, gt x y → gt y z → gt x z
  /-- Preference is irreflexive. -/
  gt_irrefl : ∀ x, ¬ gt x x
  /-- Preference is total: distinct alternatives are always comparable. -/
  gt_total : ∀ {x y}, x ≠ y → gt x y ∨ gt y x

namespace Pref

variable {A : Type v}


def top (P : Pref A) (w : A) : Pref A where
  gt x y := (x = w ∧ y ≠ w) ∨ (y ≠ w ∧ P.gt x y)
  gt_trans := by
    rintro x y z (⟨rfl, hy⟩ | ⟨hy, hxy⟩) (⟨rfl, hz⟩ | ⟨hz, hyz⟩)
    · exact absurd rfl hy
    · exact Or.inl ⟨rfl, hz⟩
    · exact absurd rfl hy
    · exact Or.inr ⟨hz, P.gt_trans hxy hyz⟩
  gt_irrefl := by
    rintro x (⟨rfl, h⟩ | ⟨-, h⟩)
    · exact h rfl
    · exact P.gt_irrefl x h
  gt_total := by
    intro x y hxy
    by_cases hx : x = w
    · exact Or.inl (Or.inl ⟨hx, fun h => hxy (hx.trans h.symm)⟩)
    · by_cases hy : y = w
      · exact Or.inr (Or.inl ⟨hy, hx⟩)
      · rcases P.gt_total hxy with h | h
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr (Or.inr ⟨hx, h⟩)

