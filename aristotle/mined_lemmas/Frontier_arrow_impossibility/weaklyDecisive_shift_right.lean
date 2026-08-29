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


theorem weaklyDecisive_shift_right (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    {S : ι → Prop} {x y z : A} (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y)
    (h : WeaklyDecisive F S x y) : WeaklyDecisive F S x z := by
  -- members of `S` rank `x ≻ y ≻ z`, everybody else ranks `y ≻ z ≻ x`
  let P1 : Pref A := three x y z base
  let P2 : Pref A := three y z x base
  let q : ι → Pref A := fun i => Pref.byProp (S i) P1 P2
  have hxy : (F q).gt x y := by
    refine h q (fun i hi => ?_) (fun i hi => ?_)
    · exact (Pref.byProp_pos hi).mpr (three_gt_fst_snd base hyx)
    · exact (Pref.byProp_neg hi).mpr (three_gt_fst_thd base hyx.symm)
  have hyz : (F q).gt y z := by
    refine hU q y z (fun i => ?_)
    by_cases hi : S i
    · exact (Pref.byProp_pos hi).mpr (three_gt_snd_thd base hyx hzx hzy)
    · exact (Pref.byProp_neg hi).mpr (three_gt_fst_snd base hzy)
  refine weaklyDecisive_of_witness hI q (fun i hi => ?_) (fun i hi => ?_) ((F q).gt_trans hxy hyz)
  · exact (Pref.byProp_pos hi).mpr (three_gt_fst_thd base hzx)
  · exact (Pref.byProp_neg hi).mpr (three_gt_snd_thd base hzy hyx.symm hzx.symm)

/-- Field expansion, step 2: shifting the first coordinate of a weakly decisive pair. -/
