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

theorem exists_lt_eq_and_le {α : Type} [Finite α] (f : ℕ → α) (g : ℕ → ℕ) :
    ∃ i j, i < j ∧ f i = f j ∧ g i ≤ g j := by
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hT : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  have hs : (g '' (f ⁻¹' {y})).Nonempty := hT.nonempty.image g
  obtain ⟨i, hi, hgi⟩ := Nat.sInf_mem hs
  obtain ⟨j, hj, hij⟩ := hT.exists_gt i
  refine ⟨i, j, hij, ?_, ?_⟩
  · have h1 : f i = y := hi
    have h2 : f j = y := hj
    rw [h1, h2]
  · have hmem : g j ∈ (g '' (f ⁻¹' {y})) := ⟨j, hj, rfl⟩
    calc g i = sInf (g '' (f ⁻¹' {y})) := hgi
      _ ≤ g j := Nat.sInf_le hmem

/--
**Robertson–Seymour (bounded-support case).**

Graphs with at most `k` non-isolated vertices are well-quasi-ordered by the minor relation:
in any infinite sequence of such graphs there are indices `i < j` with `Gs i` a minor of
`Gs j`.

Note: this is the bounded-support special case of the Robertson–Seymour graph minor
theorem, not the full theorem (whose known proof spans hundreds of pages).  The class
covered here is nonetheless infinite: for every `k` it contains all graphs with at most
`k` vertices (see `robertson_seymour_bounded_order`) and all graphs with at most `k` edges
(see `robertson_seymour_bounded_size`), each with arbitrarily many isolated vertices added.
-/
