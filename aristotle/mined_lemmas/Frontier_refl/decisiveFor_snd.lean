import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean 4 does not allow a module doc-comment to precede `import`,
so this required header is given as an ordinary block comment.)
-/

import Mathlib

/-!
Arrow's impossibility theorem.

A *preference* on a type of alternatives `A` is a linear order in the "weak" sense:
a total, transitive, antisymmetric relation `pref`, where `pref x y` reads
"`x` is at least as good as `y`".  `better x y` means `x` is strictly better than `y`.

A *social welfare function* is a map `F` from profiles (one preference per voter)
to a single preference.  Arrow's theorem says that with at least three alternatives and a
finite nonempty electorate, no such `F` can simultaneously satisfy unanimity (Pareto),
independence of irrelevant alternatives, and non-dictatorship.

The proof formalized here is the classical "decisive coalitions" argument:
the field-expansion lemma upgrades weak decisiveness over one pair to full decisiveness,
the contraction lemma splits a decisive coalition, and finiteness of the electorate then
produces a decisive singleton, i.e. a dictator.
-/

namespace Frontier

/-- A ranking of the alternatives `A`: a total, transitive, antisymmetric relation.
`pref x y` means "`x` is at least as good as `y`". -/
structure Pref (A : Type*) where
  /-- `pref x y` : the alternative `x` is at least as good as the alternative `y`. -/
  pref : A → A → Prop
  total' : ∀ x y, pref x y ∨ pref y x
  trans' : ∀ x y z, pref x y → pref y z → pref x z
  antisymm' : ∀ x y, pref x y → pref y x → x = y

namespace Pref

variable {A : Type*} (r : Pref A) {x y z b c : A}

/-- `r.better x y` : the alternative `x` is strictly better than `y` according to `r`. -/

lemma decisiveFor_snd (hU : Unanimity F) (hI : IIA F) {S : Set V} {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hW : WeaklyDecisive F S a b) :
    DecisiveFor F S c b := by
  classical
  intro q hq
  set p : V → Pref A := fun v => if v ∈ S then (q v).twoTop c a else (q v).pushBot a with hp
  have hpS : ∀ v ∈ S, p v = (q v).twoTop c a := by intro v hv; simp [hp, hv]
  have hpN : ∀ v ∉ S, p v = (q v).pushBot a := by intro v hv; simp [hp, hv]
  have h1 : (F p).better a b := by
    refine hW p (fun v hv => ?_) (fun v hv => ?_)
    · rw [hpS v hv]
      exact (q v).twoTop_better_snd hac hbc (Ne.symm hab)
    · rw [hpN v hv]; exact (q v).pushBot_better_bot (Ne.symm hab)
  have h2 : (F p).better c a := by
    refine hU p c a (fun v => ?_)
    by_cases hv : v ∈ S
    · rw [hpS v hv]; exact (q v).twoTop_better_fst hac
    · rw [hpN v hv]; exact (q v).pushBot_better_bot (Ne.symm hac)
  have h3 : (F p).better c b := (F p).better_trans h2 h1
  have hagree : ∀ v, ((p v).pref b c ↔ (q v).pref b c) := by
    intro v
    by_cases hv : v ∈ S
    · rw [hpS v hv]
      constructor
      · intro h; exact absurd h ((q v).twoTop_not_pref_fst hbc)
      · intro h; exact absurd h (hq v hv)
    · rw [hpN v hv]; exact (q v).pushBot_pref_iff (Ne.symm hab) (Ne.symm hac)
  exact (iia_better hI p q b c hagree).mp h3

/-- Field expansion lemma: weak decisiveness over a single pair implies full decisiveness. -/
