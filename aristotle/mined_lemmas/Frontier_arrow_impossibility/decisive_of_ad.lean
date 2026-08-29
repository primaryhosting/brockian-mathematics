/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment rather than a `/-!` module docstring, since Lean 4
-- requires `import` commands to precede every command, including module docstrings.)

import Mathlib

set_option maxHeartbeats 1000000

namespace Frontier

/-! ## Preferences

A *preference* on a type of alternatives `A` is a linear (total) order on `A`, presented as a
bundled relation.  This is the classical "ranked ballot" of social choice theory.
-/

/-- A ranking of the alternatives `A`: a total, transitive, antisymmetric relation. -/
structure Pref (A : Type*) where
  /-- The weak preference relation: `rel a b` means `a` is ranked at least as high as `b`. -/
  rel : A → A → Prop
  total' : ∀ a b, rel a b ∨ rel b a
  trans' : ∀ {a b c}, rel a b → rel b c → rel a c
  antisymm' : ∀ {a b}, rel a b → rel b a → a = b

namespace Pref

variable {A : Type*}

/-- Strict preference: `a` is ranked strictly above `b`. -/

lemma decisive_of_ad (hthree : ∀ x y : A, ∃ z : A, z ≠ x ∧ z ≠ y) {S : Finset V} {p q : A}
    (hpq : p ≠ q) (h : AlmostDecisive F S p q) : Decisive F S := by
  classical
  have hAD := ad_all hu hi hthree hpq h
  intro x y hxy P hin
  obtain ⟨z, hzx, hzy⟩ := hthree x y
  set Q : V → Pref A := fun i => if i ∈ S then pref3 x z y else topPref z (P i) with hQ
  have hQin : ∀ i ∈ S, Q i = pref3 x z y := by intro i hiS; simp [hQ, hiS]
  have hQout : ∀ i ∉ S, Q i = topPref z (P i) := by intro i hiS; simp [hQ, hiS]
  have hxz' : (F Q).lt x z := by
    refine hAD x z (Ne.symm hzx) Q (fun i hiS => ?_) (fun i hiS => ?_)
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hxy, hxy.symm, hzx, hzx.symm, hzy, hzy.symm])
    · rw [hQout i hiS]
      exact topPref_lt_top (Ne.symm hzx)
  have hzy' : (F Q).lt z y := by
    refine hu Q z y (fun i => ?_)
    by_cases hiS : i ∈ S
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hxy, hxy.symm, hzx, hzx.symm, hzy, hzy.symm])
    · rw [hQout i hiS]
      exact topPref_lt_top (Ne.symm hzy)
  have hxy' : (F Q).lt x y := Pref.lt_trans' hxz' hzy'
  refine (hi P Q x y (fun i => ?_)).2 hxy'
  by_cases hiS : i ∈ S
  · rw [hQin i hiS]
    exact iff_of_true (hin i hiS)
      (pref3_lt_of_key (by norm_num [key3, hxy, hxy.symm, hzx, hzx.symm, hzy, hzy.symm]))
  · rw [hQout i hiS]
    exact (topPref_lt_iff (Ne.symm hzx) (Ne.symm hzy)).symm

omit [LinearOrder A] [DecidableEq V] hi in
/-- The whole electorate is decisive, by unanimity. -/
