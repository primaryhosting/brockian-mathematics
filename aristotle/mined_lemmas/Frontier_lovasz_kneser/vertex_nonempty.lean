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

lemma vertex_nonempty {n k : ℕ} (hk : 1 ≤ k) (s : KneserVertex n k) : s.1.Nonempty :=
  Finset.card_pos.mp (by rw [s.2]; omega)

/-- The standard `(n - 2k + 2)`-coloring of the Kneser graph: a `k`-set `s` gets the color
`min (min s) (n - 2k + 1)`.  The colour classes `{s | min s = i}` for `i < n - 2k + 1` are
intersecting, and the last class consists of the `k`-subsets of the `(2k-1)`-element set
`{n - 2k + 1, …, n - 1}`, which is intersecting as well. -/
