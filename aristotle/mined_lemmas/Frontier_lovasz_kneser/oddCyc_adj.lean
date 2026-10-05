import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

/-- Vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an `n`-element set. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-subsets of `Fin n`, and two
distinct vertices are adjacent when the corresponding sets are disjoint. -/

lemma oddCyc_adj (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    (kneserGraph (2 * k + 1) k).Adj (oddCyc k j) (oddCyc k (j + 1)) := by
  refine ⟨oddCycVert_disjoint k j, ?_⟩
  intro h
  have hd := oddCycVert_disjoint k j
  rw [show oddCycVert k (j + 1) = oddCycVert k j from congrArg Subtype.val h.symm,
    disjoint_self] at hd
  have := oddCycVert_card k j
  rw [hd] at this
  simp at this
  omega

