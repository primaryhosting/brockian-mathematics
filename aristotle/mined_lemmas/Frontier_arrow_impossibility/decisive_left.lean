import Mathlib
/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- A (strict) ranking of three alternatives, given by an injective "rank" function:
`rank a < rank b` means that `a` is strictly preferred to `b`. -/
structure Ranking where
  rank : Fin 3 → Fin 3
  rank_inj : Function.Injective rank

/-- `Prefers r a b` : the ranking `r` strictly prefers `a` to `b`. -/

lemma decisive_left {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F) (hI : IIA F)
    {i : Fin 2} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : Decisive F i a b) : Decisive F i c b := by
  -- voter `i` ranks `c ≻ a ≻ b`, the other voter ranks `b ≻ c ≻ a`
  obtain ⟨r, hrca, hrab⟩ := exists_ranking (Ne.symm hac) (Ne.symm hbc) hab
  obtain ⟨s, hsbc, hsca⟩ := exists_ranking hbc hab.symm (Ne.symm hac)
  set p : Fin 2 → Ranking := mkProfile i r s
  have hpi : p i = r := mkProfile_self i r s
  have hpo : p (other i) = s := mkProfile_other i r s
  have hFca : Prefers (F p) c a := by
    refine hU p c a ?_
    intro j
    rcases eq_or_eq_other i j with rfl | rfl
    · rw [hpi]; exact hrca
    · rw [hpo]; exact hsca
  have hFab : Prefers (F p) a b := by
    refine h p ?_ ?_
    · rw [hpi]; exact hrab
    · rw [hpo]; exact hsbc.trans hsca
  have hFcb : Prefers (F p) c b := hFca.trans hFab
  intro q hqi hqo
  refine (hI p q c b ?_).mp hFcb
  intro j
  rcases eq_or_eq_other i j with rfl | rfl
  · rw [hpi]
    exact iff_of_true (hrca.trans hrab) hqi
  · rw [hpo]
    exact iff_of_false hsbc.asymm hqo.asymm

/-- Decisiveness on one pair spreads to all pairs. -/
