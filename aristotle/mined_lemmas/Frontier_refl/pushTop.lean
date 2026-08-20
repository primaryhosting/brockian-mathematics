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

def pushTop (r : Pref A) (b : A) : Pref A where
  pref x y := x = b ∨ (y ≠ b ∧ r.pref x y)
  total' x y := by
    by_cases hx : x = b
    · exact Or.inl (Or.inl hx)
    · by_cases hy : y = b
      · exact Or.inr (Or.inl hy)
      · rcases r.total' x y with h | h
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr (Or.inr ⟨hx, h⟩)
  trans' x y z h₁ h₂ := by
    rcases h₁ with rfl | ⟨hyb, hxy⟩
    · exact Or.inl rfl
    · rcases h₂ with rfl | ⟨hzb, hyz⟩
      · exact absurd rfl hyb
      · exact Or.inr ⟨hzb, r.trans' _ _ _ hxy hyz⟩
  antisymm' x y h₁ h₂ := by
    rcases h₁ with rfl | ⟨hyb, hxy⟩
    · rcases h₂ with rfl | ⟨hxb, _⟩
      · rfl
      · exact absurd rfl hxb
    · rcases h₂ with rfl | ⟨_, hyx⟩
      · exact absurd rfl hyb
      · exact r.antisymm' _ _ hxy hyx

/-- Modify `r` by moving `c` to the bottom. -/
