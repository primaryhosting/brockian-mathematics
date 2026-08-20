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

theorem arrow_dictator [Finite V] [Nonempty V] [Fintype A] (hA : 3 ≤ Fintype.card A)
    (F : (V → Pref A) → Pref A) (hU : Unanimity F) (hI : IIA F) :
    ∃ d : V, IsDictator F d := by
  classical
  have _ : Fintype V := Fintype.ofFinite V
  have hneA : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  have h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y := exists_third hA
  let r₀ : Pref A := Pref.ofInjective (Fintype.equivFin A) (Equiv.injective _)
  have huniv : Decisive F (Set.univ : Set V) := by
    intro x y _ p hp
    exact hU p x y (fun v => hp v (Set.mem_univ v))
  obtain ⟨d, hd⟩ := exists_decisive_singleton hU hI h3 r₀ Finset.univ
    (by simpa using huniv) Finset.univ_nonempty
  refine ⟨d, fun p x y hxy => ?_⟩
  refine hd x y ((p d).ne_of_better hxy) p ?_
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact hxy

/-- **Arrow's impossibility theorem**: with at least three alternatives and a finite
nonempty electorate, no social welfare function satisfies unanimity, independence of
irrelevant alternatives and non-dictatorship simultaneously. -/
