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

theorem isPlanar_K2 : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  classical
  refine ⟨K2Rot, ?_⟩
  have hc : Nat.card ((⊤ : SimpleGraph (Fin 2)).ConnectedComponent) = 1 := by
    have hs : Subsingleton ((⊤ : SimpleGraph (Fin 2)).ConnectedComponent) := by
      constructor
      intro a b
      induction a using SimpleGraph.ConnectedComponent.ind with | _ a =>
      induction b using SimpleGraph.ConnectedComponent.ind with | _ b =>
      rcases eq_or_ne a b with rfl | hab
      · rfl
      · exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hab)
    have hn : Nonempty ((⊤ : SimpleGraph (Fin 2)).ConnectedComponent) :=
      ⟨SimpleGraph.connectedComponentMk _ 0⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨hs, hn⟩
  rw [hc]
  have hE : Nat.card ((⊤ : SimpleGraph (Fin 2)).edgeSet) = 1 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]; decide
  have hne : Nonempty ((⊤ : SimpleGraph (Fin 2)).Dart) := ⟨⟨(0, 1), by simp⟩⟩
  have hF : K2Rot.faceCount = 1 := by
    apply numOrbits_eq_one
    intro a b
    have ha : a.toProd = (0, 1) ∨ a.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := a
      have hxy : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    have hb : b.toProd = (0, 1) ∨ b.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := b
      have hxy : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2
    · exact ⟨0, by simp [SimpleGraph.Dart.ext_iff, h1, h2]⟩
    · refine ⟨1, ?_⟩
      simp only [zpow_one]
      apply SimpleGraph.Dart.ext
      simp [K2Rot, SimpleGraph.Dart.symm_toProd, h1, h2, Prod.swap]
    · refine ⟨1, ?_⟩
      simp only [zpow_one]
      apply SimpleGraph.Dart.ext
      simp [K2Rot, SimpleGraph.Dart.symm_toProd, h1, h2, Prod.swap]
    · exact ⟨0, by simp [SimpleGraph.Dart.ext_iff, h1, h2]⟩
  rw [hE, hF]
  simp

end Examples

end Frontier

import RequestProject.Planar

/-!
# Greedy colouring of degenerate graphs, and the six colour theorem

A graph is `k`-degenerate if each of its nonempty (induced) subgraphs contains a vertex of degree
at most `k`; such a graph can be greedily coloured with `k + 1` colours.

Every nonempty planar graph has a vertex of degree at most `5`
(`Frontier.exists_degree_le_five`), so any graph all of whose induced subgraphs are planar is
`5`-degenerate, hence `6`-colourable. (Planarity really is inherited by induced subgraphs, so
this hypothesis holds for every planar graph; that implication is a statement about surgery on
rotation systems and is not formalised here.)
-/

namespace Frontier

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `IsDegenerate G k` says that every nonempty set of vertices contains a vertex having at most
`k` neighbours inside that set: `G` is `k`-degenerate. -/
