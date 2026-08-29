/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset SimpleGraph

/-! ## A decidable reformulation of `CliqueFree` -/

/-- `G.CliqueFree n` says: no finset of `n` pairwise-adjacent vertices. -/

theorem card_ne_of_cliqueFree {V : Type*} [DecidableEq V] {G : SimpleGraph V} {n : ℕ}
    (h : G.CliqueFree n) (s : Finset V) (hs : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b) :
    s.card ≠ n := fun hc => (cliqueFree_iff_pairwise G n).mp h s ⟨hs, hc⟩

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` holds when every graph on `n` vertices contains either a clique of
size `s` or an independent set of size `t`. -/
