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

theorem arrow_dictator {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F) (hI : IIA F) :
    ∃ d : Fin 2, IsDictator F d := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  rcases decisive_of_pair hI h01 with h | h
  · exact ⟨0, dictator_of_decisive_all hU (decisive_all hU hI h01 h)⟩
  · exact ⟨1, dictator_of_decisive_all hU (decisive_all hU hI (Ne.symm h01) h)⟩

/-- **Arrow's impossibility theorem** (base case: two voters, three alternatives).
No social welfare function on rankings of three alternatives is simultaneously unanimous,
independent of irrelevant alternatives, and non-dictatorial. -/
