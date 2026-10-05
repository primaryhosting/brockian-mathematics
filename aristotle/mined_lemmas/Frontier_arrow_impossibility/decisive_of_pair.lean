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

lemma decisive_of_pair {F : (Fin 2 → Ranking) → Ranking} (hI : IIA F) {a b : Fin 3}
    (hab : a ≠ b) : Decisive F 0 a b ∨ Decisive F 1 b a := by
  obtain ⟨c, hac, hbc⟩ := exists_third hab
  obtain ⟨r₀, hr₀ab, hr₀bc⟩ := exists_ranking hab hac hbc
  obtain ⟨r₁, hr₁ba, hr₁ac⟩ := exists_ranking hab.symm hbc hac
  set p : Fin 2 → Ranking := mkProfile 0 r₀ r₁
  have hp0 : p 0 = r₀ := mkProfile_self 0 r₀ r₁
  have hp1 : p 1 = r₁ := by
    have := mkProfile_other 0 r₀ r₁
    simpa [other] using this
  rcases prefers_total (F p) hab with hF | hF
  · left
    intro q hq0 hq1
    have hq1' : Prefers (q 1) b a := by simpa [other] using hq1
    refine (hI p q a b ?_).mp hF
    intro i
    fin_cases i
    · exact iff_of_true hr₀ab hq0
    · exact iff_of_false hr₁ba.asymm hq1'.asymm
  · right
    intro q hq1 hq0
    have hq0' : Prefers (q 0) a b := by simpa [other] using hq0
    refine (hI p q b a ?_).mp hF
    intro i
    fin_cases i
    · exact iff_of_false hr₀ab.asymm hq0'.asymm
    · exact iff_of_true hr₁ba hq1

/-- Expansion: decisiveness on `(a,b)` gives decisiveness on `(a,c)`. -/
