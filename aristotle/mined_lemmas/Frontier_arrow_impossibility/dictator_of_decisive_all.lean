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

lemma dictator_of_decisive_all {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F)
    {i : Fin 2} (h : ∀ x y : Fin 3, x ≠ y → Decisive F i x y) : IsDictator F i := by
  intro p x y hxy
  rcases prefers_total (p (other i)) hxy.ne with hother | hother
  · refine hU p x y ?_
    intro j
    rcases eq_or_eq_other i j with rfl | rfl
    · exact hxy
    · exact hother
  · exact h x y hxy.ne p hxy hother

/-- **Arrow's theorem** (base case: two voters, three alternatives): unanimity and IIA force
a dictator. -/
