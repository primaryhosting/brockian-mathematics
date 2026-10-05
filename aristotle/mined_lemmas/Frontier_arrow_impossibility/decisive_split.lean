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


theorem decisive_split (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    (hthird : ∀ x y : A, ∃ t : A, t ≠ x ∧ t ≠ y) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {S S₁ S₂ : ι → Prop} (hS : ∀ i, S i ↔ (S₁ i ∨ S₂ i)) (hdisj : ∀ i, ¬ (S₁ i ∧ S₂ i))
    (hdec : Decisive F S) : Decisive F S₁ ∨ Decisive F S₂ := by
  -- `S₁` ranks `a ≻ b ≻ c`, `S₂` ranks `b ≻ c ≻ a`, everybody else ranks `c ≻ a ≻ b`
  let P1 : Pref A := three a b c base
  let P2 : Pref A := three b c a base
  let P3 : Pref A := three c a b base
  let q : ι → Pref A := fun i => Pref.byProp (S₁ i) P1 (Pref.byProp (S₂ i) P2 P3)
  have hq1 : ∀ i, S₁ i → ∀ {x y : A}, ((q i).gt x y ↔ P1.gt x y) :=
    fun i hi => Pref.byProp_pos hi
  have hq2 : ∀ i, S₂ i → ∀ {x y : A}, ((q i).gt x y ↔ P2.gt x y) := by
    intro i hi x y
    have hi1 : ¬ S₁ i := fun h => hdisj i ⟨h, hi⟩
    exact (Pref.byProp_neg hi1).trans (Pref.byProp_pos hi)
  have hq3 : ∀ i, ¬ S i → ∀ {x y : A}, ((q i).gt x y ↔ P3.gt x y) := by
    intro i hi x y
    have hi1 : ¬ S₁ i := fun h => hi ((hS i).mpr (Or.inl h))
    have hi2 : ¬ S₂ i := fun h => hi ((hS i).mpr (Or.inr h))
    exact (Pref.byProp_neg hi1).trans (Pref.byProp_neg hi2)
  -- society prefers `b` to `c`, since the decisive coalition `S` does
  have hbc' : (F q).gt b c := by
    refine hdec q b c hbc (fun i hi => ?_)
    rcases (hS i).mp hi with h1 | h2
    · exact (hq1 i h1).mpr (three_gt_snd_thd base hab.symm hac.symm hbc.symm)
    · exact (hq2 i h2).mpr (three_gt_fst_snd base hbc.symm)
  rcases (F q).gt_total hac with hf | hf
  · -- society prefers `a` to `c`, and only `S₁` does
    left
    refine decisive_of_weaklyDecisive base hU hI hthird hac
      (weaklyDecisive_of_witness hI q (fun i hi => ?_) (fun i hi => ?_) hf)
    · exact (hq1 i hi).mpr (three_gt_fst_thd base hac.symm)
    · by_cases hiS : S i
      · have h2 : S₂ i := by
          rcases (hS i).mp hiS with h | h
          · exact absurd h hi
          · exact h
        exact (hq2 i h2).mpr (three_gt_snd_thd base hbc.symm hab hac)
      · exact (hq3 i hiS).mpr (three_gt_fst_snd base hac)
  · -- society prefers `c` to `a`, hence `b` to `a`, and only `S₂` prefers `b` to `a`
    right
    have hba : (F q).gt b a := (F q).gt_trans hbc' hf
    refine decisive_of_weaklyDecisive base hU hI hthird hab.symm
      (weaklyDecisive_of_witness hI q (fun i hi => ?_) (fun i hi => ?_) hba)
    · exact (hq2 i hi).mpr (three_gt_fst_thd base hab)
    · by_cases hiS : S i
      · have h1 : S₁ i := by
          rcases (hS i).mp hiS with h | h
          · exact h
          · exact absurd h hi
        exact (hq1 i h1).mpr (three_gt_fst_snd base hab.symm)
      · exact (hq3 i hiS).mpr (three_gt_snd_thd base hac hbc hab.symm)

/-- Induction along a list enumerating the electorate: every decisive coalition contained in the
list contains a decisive singleton. -/
