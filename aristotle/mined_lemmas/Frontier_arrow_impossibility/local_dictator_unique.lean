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
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- verbatim as the module docstring below.)

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*} {n : ℕ}

/-! ## Rankings and profiles -/

/-- `r` is a strict ranking (irreflexive, transitive, total) of the alternatives. -/
structure IsRanking (r : A → A → Prop) : Prop where
  asymm : ∀ x y, r x y → ¬ r y x
  trans' : ∀ x y z, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x


lemma local_dictator_unique (S : SWF A n) {u v w : Fin n} {p q s : A}
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hu : ∀ Q, IsProfile Q → ∀ x y, x ≠ p → y ≠ p → Q u x y → S.F Q x y)
    (hv : ∀ Q, IsProfile Q → ∀ x y, x ≠ q → y ≠ q → Q v x y → S.F Q x y)
    (hw : ∀ Q, IsProfile Q → ∀ x y, x ≠ s → y ≠ s → Q w x y → S.F Q x y) :
    u = v := by
  classical
  by_contra huv
  obtain ⟨r, hr⟩ := exists_ranking A
  -- a Condorcet-style cyclic profile
  set Q : Fin n → A → A → Prop :=
    fun i => if i = v then byRank (rank3 q p s) r else byRank (rank3 s q p) r with hQdef
  have hQv : Q v = byRank (rank3 q p s) r := by simp only [hQdef, if_pos rfl]
  have hQother : ∀ i, i ≠ v → Q i = byRank (rank3 s q p) r := by
    intro i h; simp only [hQdef, if_neg h]
  have hQ : IsProfile Q := by
    intro i
    by_cases h : i = v
    · rw [h, hQv]; exact isRanking_byRank _ hr
    · rw [hQother i h]; exact isRanking_byRank _ hr
  have hQu : Q u s q := by
    rw [hQother u huv]
    exact byRank_of_lt (by simp [rank3, hqs])
  have hQvp : Q v p s := by
    rw [hQv]
    exact byRank_of_lt (by simp [rank3, hpq, hps.symm, hqs.symm])
  have hQw : Q w q p := by
    by_cases hwv : w = v
    · rw [hwv, hQv]
      exact byRank_of_lt (by simp [rank3, hpq])
    · rw [hQother w hwv]
      exact byRank_of_lt (by simp [rank3, hpq, hps, hqs])
  have h1 : S.F Q s q := hu Q hQ s q (Ne.symm hps) (Ne.symm hpq) hQu
  have h2 : S.F Q q p := hw Q hQ q p hqs hps hQw
  have h3 : S.F Q p s := hv Q hQ p s hpq (Ne.symm hqs) hQvp
  have h4 : S.F Q s p := (S.rational Q hQ).trans' _ _ _ h1 h2
  exact (S.rational Q hQ).asymm _ _ h4 h3

/-! ## Arrow's theorem -/

/-- **Arrow's theorem**: on at least three alternatives, every rational, unanimous social
welfare function satisfying independence of irrelevant alternatives has a dictator. -/
