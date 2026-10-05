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

lemma prefers_total (r : Ranking) {a b : Fin 3} (hab : a ≠ b) :
    Prefers r a b ∨ Prefers r b a := by
  rcases lt_trichotomy (r.rank a) (r.rank b) with h | h | h
  · exact Or.inl h
  · exact absurd (r.rank_inj h) hab
  · exact Or.inr h

/-- Existence of a ranking realising a prescribed strict order `a ≻ b ≻ c`. -/
