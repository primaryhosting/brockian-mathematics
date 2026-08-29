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

/-! ## The Kneser graph -/

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

lemma arcVertex_adj (hk : 1 ≤ k) (i : ℕ) :
    (kneserGraph (2 * k + 1) k).Adj (arcVertex k (i + k)) (arcVertex k i) := by
  have hd : Disjoint (arc k i) (arc k (i + k)) := arc_disjoint k i
  have hnonempty : (arc k i).Nonempty := by
    rw [← Finset.card_pos, arc_card]
    omega
  obtain ⟨x, hx⟩ := hnonempty
  refine ⟨fun h => ?_, hd.symm⟩
  have h' : arc k (i + k) = arc k i := congrArg Subtype.val h
  exact (Finset.disjoint_left.mp hd hx) (h' ▸ hx)

/-- `KG_{2k+1,k}` is not `2`-colourable: the arcs `arc k (m * k)`, `m = 0, …, 2k`, form a
cycle of odd length `2k + 1`. -/
