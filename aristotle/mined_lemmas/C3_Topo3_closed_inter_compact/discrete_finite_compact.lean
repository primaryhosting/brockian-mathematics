import Mathlib
namespace C3.Topo3

/-- The intersection of a compact set with a closed set is compact. -/

theorem discrete_finite_compact {X : Type*} [TopologicalSpace X] [Fintype X] (s : Set X) :
    IsCompact s :=
  (Set.toFinite s).isCompact

/-- Constant maps are continuous. -/
