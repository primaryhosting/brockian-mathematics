import Mathlib
namespace C6.T4

theorem inter_closed {X : Type*} [TopologicalSpace X] (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ t) := hs.inter ht
