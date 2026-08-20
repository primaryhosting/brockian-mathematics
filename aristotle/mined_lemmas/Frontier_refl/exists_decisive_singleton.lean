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

lemma exists_decisive_singleton [Nonempty A] [DecidableEq V] (hU : Unanimity F) (hI : IIA F)
    (h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y) (r₀ : Pref A) :
    ∀ S : Finset V, Decisive F (↑S : Set V) → S.Nonempty → ∃ d : V, Decisive F {d} := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hS hne
    obtain ⟨d, hd⟩ := hne
    by_cases hcard : S.erase d = ∅
    · refine ⟨d, ?_⟩
      have hSd : (↑S : Set V) = {d} := by
        ext x
        simp only [Finset.mem_coe, Set.mem_singleton_iff]
        constructor
        · intro hx
          by_contra hxd
          have : x ∈ S.erase d := Finset.mem_erase.mpr ⟨hxd, hx⟩
          rw [hcard] at this
          simp at this
        · rintro rfl; exact hd
      rwa [hSd] at hS
    · have hsplit : (↑S : Set V) = {d} ∪ ↑(S.erase d) := by
        ext x
        simp only [Finset.mem_coe, Set.mem_union, Set.mem_singleton_iff, Finset.mem_erase]
        constructor
        · intro hx
          by_cases h : x = d
          · exact Or.inl h
          · exact Or.inr ⟨h, hx⟩
        · rintro (rfl | ⟨-, hx⟩)
          · exact hd
          · exact hx
      have hdisj : Disjoint ({d} : Set V) (↑(S.erase d) : Set V) := by
        rw [Set.disjoint_singleton_left]
        simp
      rw [hsplit] at hS
      rcases decisive_split hU hI h3 r₀ hdisj hS with h | h
      · exact ⟨d, h⟩
      · exact ih (S.erase d) (Finset.erase_ssubset hd) h (Finset.nonempty_of_ne_empty hcard)

end Proof

section Main

variable {V A : Type*}

/-- If there are at least three alternatives, then for any two of them there is a third. -/
