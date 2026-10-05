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

theorem cliqueFree_iff_pairwise {V : Type*} [DecidableEq V] (G : SimpleGraph V) (n : ℕ) :
    G.CliqueFree n ↔ ∀ s : Finset V, ¬ ((∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b) ∧ s.card = n) := by
  constructor
  · intro h s hs
    exact h s ⟨fun a ha b hb hab => hs.1 a ha b hb hab, hs.2⟩
  · intro h s hs
    exact h s ⟨fun a ha b hb hab => hs.1 ha hb hab, hs.2⟩

/-- From cliquefreeness: a set of pairwise adjacent vertices cannot have `n` elements. -/
