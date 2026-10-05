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

lemma lovasz_kneser_one (n : ℕ) (hn : 2 ≤ n) :
    (kneserGraph n 1).chromaticNumber = (n - 2 * 1 + 2 : ℕ) := by
  rw [kneserGraph_one_eq_top, SimpleGraph.chromaticNumber_top]
  have hcard : Fintype.card (KneserVertex n 1) = n := by
    rw [Fintype.card_finset_len]
    simp
  rw [hcard]
  congr 1
  omega

/-- `KG_{2k,k}` has an edge: the first `k` and the last `k` elements of `Fin (2k)`. -/
