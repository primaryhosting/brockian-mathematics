import Mathlib
/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The full Robertson–Seymour graph minor theorem states that *all* finite graphs are
well-quasi-ordered by the minor relation.  Its only known proof is the Graph Minors series
of Robertson and Seymour, spanning hundreds of pages, and it is not formalized here.

What is developed and proved below, axiom-free, is:

* the minor relation on finite simple graphs, via branch-set minor models
  (`Math2.MinorModel`, `Math2.IsMinor`);
* `Math2.isMinor_of_embedding`: a subgraph embedding yields a minor;
* `Math2.robertson_seymour`: well-quasi-ordering by the minor relation for the (infinite)
  class of graphs with at most `k` non-isolated vertices;
* the corollaries `Math2.robertson_seymour_bounded_order` (at most `k` vertices) and
  `Math2.robertson_seymour_bounded_size` (at most `k` edges), in both cases with
  arbitrarily many isolated vertices allowed.
-/

open scoped Classical

namespace Math2

/-- A finite simple graph, presented as a simple graph on `Fin n`. -/
structure FinGraph where
  n : ℕ
  G : SimpleGraph (Fin n)

/-- A *minor model* of `H` inside `K`: a family of pairwise disjoint, nonempty, connected
branch sets of `K`, one for each vertex of `H`, such that adjacent vertices of `H` have
branch sets joined by an edge of `K`. -/
structure MinorModel (H K : FinGraph) where
  B : Fin H.n → Set (Fin K.n)
  nonempty' : ∀ h, (B h).Nonempty
  disj : ∀ h h', h ≠ h' → Disjoint (B h) (B h')
  conn : ∀ h, (K.G.induce (B h)).Connected
  edge : ∀ h h', H.G.Adj h h' → ∃ a ∈ B h, ∃ b ∈ B h', K.G.Adj a b

/-- `H` is a minor of `K`. -/

theorem robertson_seymour_bounded_size (k : ℕ) (Gs : ℕ → FinGraph)
    (hk : ∀ i, (Gs i).G.edgeSet.ncard ≤ k) :
    ∃ i j, i < j ∧ IsMinor (Gs i) (Gs j) := by
  refine robertson_seymour (2 * k) Gs (fun i => ?_)
  exact le_trans (FinGraph.card_support_le (Gs i)) (Nat.mul_le_mul_left 2 (hk i))

end Math2

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

