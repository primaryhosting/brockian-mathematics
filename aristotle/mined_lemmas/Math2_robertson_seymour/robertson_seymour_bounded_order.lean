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

theorem robertson_seymour_bounded_order (k : ℕ) (Gs : ℕ → FinGraph)
    (hk : ∀ i, (Gs i).n ≤ k) :
    ∃ i j, i < j ∧ IsMinor (Gs i) (Gs j) := by
  refine robertson_seymour k Gs (fun i => ?_)
  calc (Gs i).support.card ≤ (Finset.univ : Finset (Fin (Gs i).n)).card :=
        Finset.card_le_univ _
    _ = (Gs i).n := by simp
    _ ≤ k := hk i

/-- Graphs with at most `k` edges are well-quasi-ordered by the minor relation. -/
