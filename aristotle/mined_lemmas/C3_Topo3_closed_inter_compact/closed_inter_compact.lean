import Mathlib
namespace C3.Topo3

/-- The intersection of a compact set with a closed set is compact. -/

theorem closed_inter_compact {X : Type*} [TopologicalSpace X] (s t : Set X)
    (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t) :=
  hs.inter_right ht

/-- Every subset of a finite topological space is compact. -/
