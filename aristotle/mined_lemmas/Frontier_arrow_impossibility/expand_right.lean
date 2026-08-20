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

lemma expand_right (hU : Unanimous F) (hI : IIA F) {G : Finset V} {a b c : α}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (h : AlmostDecisiveFor F G a b) :
    DecisiveFor F G a c := by
  classical
  intro p hp
  set q : V → Ranking α :=
    fun i => if i ∈ G then moveTop a (moveTop b (p i)) else moveTop b (p i) with hq
  have hqin : ∀ i ∈ G, q i = moveTop a (moveTop b (p i)) := by
    intro i hi; simp [hq, hi]
  have hqout : ∀ i ∉ G, q i = moveTop b (p i) := by
    intro i hi; simp [hq, hi]
  -- everybody prefers `b` to `c`
  have hbc : ∀ i, (q i).pref b c := by
    intro i
    by_cases hi : i ∈ G
    · rw [hqin i hi, moveTop_pref a _ (Ne.symm hab) hca]
      exact moveTop_pref_top b _ hcb
    · rw [hqout i hi]
      exact moveTop_pref_top b _ hcb
  -- `G` prefers `a` to `b`, everybody else prefers `b` to `a`
  have hGab : ∀ i ∈ G, (q i).pref a b := by
    intro i hi
    rw [hqin i hi]
    exact moveTop_pref_top a _ (Ne.symm hab)
  have hGba : ∀ i ∉ G, (q i).pref b a := by
    intro i hi
    rw [hqout i hi]
    exact moveTop_pref_top b _ hab
  have h1 : (F q).pref b c := hU q b c hbc
  have h2 : (F q).pref a b := h q hGab hGba
  have h3 : (F q).pref a c := (F q).pref_trans h2 h1
  refine (hI p q a c ?_).mpr h3
  intro i
  by_cases hi : i ∈ G
  · have hq' : (q i).pref a c := by
      rw [hqin i hi]; exact moveTop_pref_top a _ hca
    exact iff_of_true (hp i hi) hq'
  · rw [hqout i hi, moveTop_pref b _ hab hcb]

/-- **Field expansion, left**: an almost decisive coalition for `(a, b)` is decisive
for `(c, b)`, for any third alternative `c`. -/
