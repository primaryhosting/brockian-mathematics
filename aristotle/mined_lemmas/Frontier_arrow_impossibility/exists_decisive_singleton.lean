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


theorem exists_decisive_singleton (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    (hthird : ∀ x y : A, ∃ t : A, t ≠ x ∧ t ≠ y) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (l : List ι) (S : ι → Prop), (∀ i, S i → i ∈ l) → Decisive F S →
      ∃ i : ι, Decisive F (fun j => j = i) := by
  intro l
  induction l with
  | nil =>
    intro S hsub hdec
    exact absurd hdec (not_decisive_of_isEmpty base hab (fun i hi => by
      cases hsub i hi))
  | cons a' t ih =>
    intro S hsub hdec
    have hsplit := decisive_split base hU hI hthird hab hac hbc
      (S := S) (S₁ := fun i => S i ∧ i = a') (S₂ := fun i => S i ∧ i ≠ a')
      (fun i => by
        constructor
        · intro hi
          by_cases h : i = a'
          · exact Or.inl ⟨hi, h⟩
          · exact Or.inr ⟨hi, h⟩
        · rintro (⟨hi, -⟩ | ⟨hi, -⟩) <;> exact hi)
      (fun i hi => hi.2.2 hi.1.2) hdec
    rcases hsplit with h1 | h2
    · exact ⟨a', decisive_mono (fun i hi => hi.2) h1⟩
    · refine ih (fun i => S i ∧ i ≠ a') (fun i hi => ?_) h2
      rcases List.mem_cons.mp (hsub i hi.1) with h | h
      · exact absurd h hi.2
      · exact h

/-- With at least three alternatives, for every pair of alternatives there is a third one
distinct from both. -/
