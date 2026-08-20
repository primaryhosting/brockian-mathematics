import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem numOrbits_eq_one [Nonempty α] (f : Equiv.Perm α)
    (h : ∀ a b : α, ∃ k : ℤ, (f ^ k) a = b) : numOrbits f = 1 := by
  have hs : Subsingleton (Quotient (orbitSetoid f)) := by
    constructor
    intro a b
    induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
    exact Quotient.sound (h a b)
  have hn : Nonempty (Quotient (orbitSetoid f)) := ⟨Quotient.mk _ (Classical.arbitrary α)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hs, hn⟩

end Frontier

import RequestProject.Orbits

/-!
# Combinatorial planarity, Euler's formula and the degree bound

A *combinatorial embedding* (rotation system) of a simple graph `G` consists of a permutation
`rot` of the darts (directed edges) of `G` which fixes the source of every dart and acts
transitively on the darts emanating from any fixed vertex; `rot` records the cyclic order in
which the edges around a vertex are met when walking around that vertex in the surface.

The *faces* of such an embedding are the orbits of `rot ∘ symm`, where `symm` reverses a dart.
A connected graph with at least one edge, embedded in a closed orientable surface of genus `g`,
satisfies `#V - #E + #F = 2 - 2g`, so the embedding is a plane (equivalently, sphere) embedding
exactly when the Euler characteristic attains its maximal value `2`. Summing over the `c`
connected components of a graph -- and correcting for isolated vertices, which carry no dart and
hence contribute no orbit -- gives the definition `Frontier.IsPlanar` below: `G` is planar when
some rotation system satisfies `#V - #E + #F + #(isolated vertices) ≥ 2c`.

From this we derive, by the classical face-counting argument, the bound `#E ≤ 3 #V - 6`, its
triangle-free refinement `#E ≤ 2 #V - 4`, and the existence of a vertex of small degree in any
nonempty planar graph.
-/

namespace Frontier

open SimpleGraph

variable {V : Type*}

instance instFiniteDart [Finite V] (G : SimpleGraph V) : Finite G.Dart :=
  Finite.of_injective (fun d => d.toProd) (fun _ _ h => SimpleGraph.Dart.ext _ _ h)

/-- Reversal of darts, as a permutation of the darts of `G`. -/
