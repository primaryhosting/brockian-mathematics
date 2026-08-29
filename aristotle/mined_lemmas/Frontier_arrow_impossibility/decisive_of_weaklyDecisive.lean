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


theorem decisive_of_weaklyDecisive (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    (hthird : ∀ x y : A, ∃ t : A, t ≠ x ∧ t ≠ y) {S : ι → Prop} {x y : A} (hxy : x ≠ y)
    (h : WeaklyDecisive F S x y) : Decisive F S := by
  have hall := weaklyDecisive_all base hU hI hthird hxy h
  intro p u v huv hp
  obtain ⟨w, hwu, hwv⟩ := hthird u v
  -- members of `S` rank `u ≻ w ≻ v`; everybody else keeps their preference but moves `w` on top
  let q : ι → Pref A := fun i => Pref.byProp (S i) (three u w v (p i)) ((p i).top w)
  have huw : (F q).gt u w := by
    refine hall u w (Ne.symm hwu) q (fun i hi => ?_) (fun i hi => ?_)
    · exact (Pref.byProp_pos hi).mpr (three_gt_fst_snd (p i) hwu)
    · exact (Pref.byProp_neg hi).mpr ((p i).top_gt_top (Ne.symm hwu))
  have hwv' : (F q).gt w v := by
    refine hU q w v (fun i => ?_)
    by_cases hi : S i
    · exact (Pref.byProp_pos hi).mpr
        (three_gt_snd_thd (p i) hwu (Ne.symm huv) (Ne.symm hwv))
    · exact (Pref.byProp_neg hi).mpr ((p i).top_gt_top (Ne.symm hwv))
  refine (hI p q u v ?_).mpr ((F q).gt_trans huw hwv')
  intro i
  by_cases hi : S i
  · exact ⟨fun _ => (Pref.byProp_pos hi).mpr (three_gt_fst_thd (p i) (Ne.symm huv)),
      fun _ => hp i hi⟩
  · exact ((Pref.byProp_neg hi).trans ((p i).top_gt_iff (Ne.symm hwu) (Ne.symm hwv))).symm

/-- The whole electorate is decisive. -/
