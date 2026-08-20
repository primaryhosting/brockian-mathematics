/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A ranked voting rule (social welfare function) turns a profile of individual rankings of the
alternatives into a social ranking.  Arrow's theorem says that as soon as there are at least
three alternatives, no such rule can be unanimous (Pareto), independent of irrelevant
alternatives, and non-dictatorial at the same time.

The key intermediate result is the *field expansion* / contagion lemma
`Frontier.decisive_of_almostDecisiveFor`: a coalition that gets its way on one ordered pair of
alternatives against unanimous opposition is decisive for *every* ordered pair.  A minimal
decisive coalition is then shown to be a singleton, i.e. a dictator.
-/

namespace Frontier

/-- A *ranking* of the alternatives `α`: a total, transitive, antisymmetric relation, i.e. a
linear order given as a relation.  `rel x y` reads "`x` is at least as good as `y`". -/
structure Ranking (α : Type*) where
  rel : α → α → Prop
  rel_total : ∀ x y, rel x y ∨ rel y x
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y

namespace Ranking

variable {α : Type*}

/-- Strict preference: `x` is ranked strictly above `y`. -/

lemma expand_left (hU : Unanimous F) (hI : IIA F) {G : Finset V} {a b c : α}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (h : AlmostDecisiveFor F G a b) :
    DecisiveFor F G c b := by
  classical
  intro p hp
  set q : V → Ranking α :=
    fun i => if i ∈ G then moveBot b (moveBot a (p i)) else moveBot a (p i) with hq
  have hqin : ∀ i ∈ G, q i = moveBot b (moveBot a (p i)) := by
    intro i hi; simp [hq, hi]
  have hqout : ∀ i ∉ G, q i = moveBot a (p i) := by
    intro i hi; simp [hq, hi]
  -- everybody prefers `c` to `a`
  have hca' : ∀ i, (q i).pref c a := by
    intro i
    by_cases hi : i ∈ G
    · rw [hqin i hi, moveBot_pref b _ hcb hab]
      exact moveBot_pref_bot a _ hca
    · rw [hqout i hi]
      exact moveBot_pref_bot a _ hca
  -- `G` prefers `a` to `b`, everybody else prefers `b` to `a`
  have hGab : ∀ i ∈ G, (q i).pref a b := by
    intro i hi
    rw [hqin i hi]
    exact moveBot_pref_bot b _ hab
  have hGba : ∀ i ∉ G, (q i).pref b a := by
    intro i hi
    rw [hqout i hi]
    exact moveBot_pref_bot a _ (Ne.symm hab)
  have h1 : (F q).pref c a := hU q c a hca'
  have h2 : (F q).pref a b := h q hGab hGba
  have h3 : (F q).pref c b := (F q).pref_trans h1 h2
  refine (hI p q c b ?_).mpr h3
  intro i
  by_cases hi : i ∈ G
  · have hq' : (q i).pref c b := by
      rw [hqin i hi]; exact moveBot_pref_bot b _ hcb
    exact iff_of_true (hp i hi) hq'
  · rw [hqout i hi, moveBot_pref a _ hca (Ne.symm hab)]

/-- From an almost decisive coalition for `(u, v)` we obtain decisiveness for `(u, w)` and for
`(w, v)`, for any third alternative `w`. -/
