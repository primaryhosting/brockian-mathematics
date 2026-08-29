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

lemma kneser_two_k_not_colorable_one (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k) k).Colorable 1 := by
  rintro ⟨C⟩
  obtain ⟨s, t, hst⟩ := kneser_two_k_has_edge k hk
  exact C.valid hst (Subsingleton.elim _ _)

/-- For `n = 2k` (with `k ≥ 1`) the Kneser graph is a perfect matching, of chromatic number
`2 = n - 2k + 2`. -/
