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

lemma decisive_of_weaklyDecisive (hU : Unanimity F) (hI : IIA F)
    (h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y) {S : Set V} {a b : A} (hab : a ≠ b)
    (hW : WeaklyDecisive F S a b) : Decisive F S := by
  obtain ⟨c, hca, hcb⟩ := h3 a b
  -- `a` is decisive against every other alternative
  have step1 : ∀ t, t ≠ a → t ≠ b → DecisiveFor F S a t := fun t hta htb =>
    decisiveFor_fst hU hI hab (Ne.symm hta) (Ne.symm htb) hW
  -- a chain of six applications yields decisiveness for `(a, b)` itself
  have dac : DecisiveFor F S a c := step1 c hca hcb
  have dbc : DecisiveFor F S b c :=
    decisiveFor_snd hU hI (Ne.symm hca) hab hcb
      (weaklyDecisive_of_decisiveFor dac)
  have dba : DecisiveFor F S b a :=
    decisiveFor_fst hU hI (Ne.symm hcb) (Ne.symm hab) hca
      (weaklyDecisive_of_decisiveFor dbc)
  have dca : DecisiveFor F S c a :=
    decisiveFor_snd hU hI (Ne.symm hab) (Ne.symm hcb) (Ne.symm hca)
      (weaklyDecisive_of_decisiveFor dba)
  have dcb : DecisiveFor F S c b :=
    decisiveFor_fst hU hI hca hcb hab
      (weaklyDecisive_of_decisiveFor dca)
  have dab : DecisiveFor F S a b :=
    decisiveFor_snd hU hI hcb hca (Ne.symm hab)
      (weaklyDecisive_of_decisiveFor dcb)
  have hall : ∀ t, t ≠ a → DecisiveFor F S a t := by
    intro t hta
    by_cases htb : t = b
    · subst htb; exact dab
    · exact step1 t hta htb
  intro x y hxy
  by_cases hxa : x = a
  · subst hxa; exact hall y (Ne.symm hxy)
  · by_cases hya : y = a
    · subst hya
      obtain ⟨w, hwx, hwy⟩ := h3 x y
      have dxw : DecisiveFor F S x w :=
        decisiveFor_snd hU hI (Ne.symm hwy) (Ne.symm hxa) hwx
          (weaklyDecisive_of_decisiveFor (hall w hwy))
      exact decisiveFor_fst hU hI (Ne.symm hwx) hxa hwy
        (weaklyDecisive_of_decisiveFor dxw)
    · exact decisiveFor_snd hU hI (Ne.symm hya) (Ne.symm hxa) (Ne.symm hxy)
        (weaklyDecisive_of_decisiveFor (hall y hya))

/-- Three distinct alternatives exist. -/
