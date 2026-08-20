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

lemma decisive_split [Nonempty A] (hU : Unanimity F) (hI : IIA F)
    (h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y) (r₀ : Pref A)
    {S₁ S₂ : Set V} (hdisj : Disjoint S₁ S₂) (hD : Decisive F (S₁ ∪ S₂)) :
    Decisive F S₁ ∨ Decisive F S₂ := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := exists_three (A := A) h3
  -- members of `S₁` rank `a > b > c`, members of `S₂` rank `c > a > b`,
  -- and everybody else ranks `b > c > a`
  set p : V → Pref A := fun v =>
    if v ∈ S₁ then r₀.twoTop a b else if v ∈ S₂ then r₀.twoTop c a else r₀.twoTop b c with hp
  have hp1 : ∀ v ∈ S₁, p v = r₀.twoTop a b := by intro v hv; simp [hp, hv]
  have hp2 : ∀ v, v ∉ S₁ → v ∈ S₂ → p v = r₀.twoTop c a := by
    intro v h1 h2; simp [hp, h1, h2]
  have hp3 : ∀ v, v ∉ S₁ → v ∉ S₂ → p v = r₀.twoTop b c := by
    intro v h1 h2; simp [hp, h1, h2]
  have hnot : ∀ v ∈ S₂, v ∉ S₁ := fun v hv h1 => (Set.disjoint_left.mp hdisj h1) hv
  have hab' : (F p).better a b := by
    refine hD a b hab p (fun v hv => ?_)
    rcases hv with hv | hv
    · rw [hp1 v hv]; exact r₀.twoTop_better_fst (Ne.symm hab)
    · rw [hp2 v (hnot v hv) hv]
      exact r₀.twoTop_better_snd hac hbc (Ne.symm hab)
  by_cases hcase : (F p).better a c
  · -- then `S₁` is weakly decisive for `(a, c)`
    left
    refine decisive_of_weaklyDecisive hU hI h3 hac ?_
    intro q hq1 hq2
    have hagree : ∀ v, ((p v).pref c a ↔ (q v).pref c a) := by
      intro v
      by_cases hv : v ∈ S₁
      · rw [hp1 v hv]
        constructor
        · intro h; exact absurd h (r₀.twoTop_not_pref_fst (Ne.symm hac))
        · intro h; exact absurd h (hq1 v hv)
      · have hqv : (q v).pref c a := (q v).pref_of_better (hq2 v hv)
        by_cases hv2 : v ∈ S₂
        · rw [hp2 v hv hv2]
          simp only [hqv, iff_true]
          exact (r₀.twoTop c a).pref_of_better (r₀.twoTop_better_fst hac)
        · rw [hp3 v hv hv2]
          simp only [hqv, iff_true]
          exact r₀.twoTop_pref_snd (Ne.symm hbc) hab hac
    exact (iia_better hI p q c a hagree).mp hcase
  · -- otherwise `S₂` is weakly decisive for `(c, b)`
    right
    have hpca : (F p).pref c a := not_not.mp hcase
    have hcb' : (F p).better c b := (F p).better_of_pref_of_better hpca hab'
    refine decisive_of_weaklyDecisive hU hI h3 (Ne.symm hbc) ?_
    intro q hq1 hq2
    have hagree : ∀ v, ((p v).pref b c ↔ (q v).pref b c) := by
      intro v
      by_cases hv2 : v ∈ S₂
      · rw [hp2 v (hnot v hv2) hv2]
        constructor
        · intro h; exact absurd h (r₀.twoTop_not_pref_fst hbc)
        · intro h; exact absurd h (hq1 v hv2)
      · have hqv : (q v).pref b c := (q v).pref_of_better (hq2 v hv2)
        by_cases hv1 : v ∈ S₁
        · rw [hp1 v hv1]
          simp only [hqv, iff_true]
          exact r₀.twoTop_pref_snd (Ne.symm hab) (Ne.symm hac) (Ne.symm hbc)
        · rw [hp3 v hv1 hv2]
          simp only [hqv, iff_true]
          exact (r₀.twoTop b c).pref_of_better (r₀.twoTop_better_fst (Ne.symm hbc))
    exact (iia_better hI p q b c hagree).mp hcb'

/-- Iterating the contraction lemma over a finite electorate produces a decisive singleton. -/
