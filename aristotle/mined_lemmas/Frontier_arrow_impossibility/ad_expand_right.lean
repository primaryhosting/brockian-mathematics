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

lemma ad_expand_right {S : Finset V} {a b c : A} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (h : AlmostDecisive F S a b) : AlmostDecisive F S a c := by
  classical
  set Q : V → Pref A := fun i => if i ∈ S then pref3 a b c else pref3 b c a with hQ
  have hQin : ∀ i ∈ S, Q i = pref3 a b c := by intro i hiS; simp [hQ, hiS]
  have hQout : ∀ i ∉ S, Q i = pref3 b c a := by intro i hiS; simp [hQ, hiS]
  -- society prefers `a` to `b`
  have hab' : (F Q).lt a b := by
    refine h Q (fun i hiS => ?_) (fun i hiS => ?_)
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
    · rw [hQout i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
  -- society prefers `b` to `c` by unanimity
  have hbc' : (F Q).lt b c := by
    refine hu Q b c (fun i => ?_)
    by_cases hiS : i ∈ S
    · rw [hQin i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
    · rw [hQout i hiS]
      exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])
  have hac' : (F Q).lt a c := Pref.lt_trans' hab' hbc'
  intro P hin hout
  refine (hi P Q a c (fun i => ?_)).2 hac'
  by_cases hiS : i ∈ S
  · rw [hQin i hiS]
    exact iff_of_true (hin i hiS)
      (pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm]))
  · rw [hQout i hiS]
    refine iff_of_false (Pref.not_lt_of_lt (hout i hiS)) (Pref.not_lt_of_lt ?_)
    exact pref3_lt_of_key (by norm_num [key3, hab, hab.symm, hca, hca.symm, hcb, hcb.symm])

/-- Field expansion, part 2: almost decisive for `(a,b)` implies almost decisive for `(c,b)`. -/
