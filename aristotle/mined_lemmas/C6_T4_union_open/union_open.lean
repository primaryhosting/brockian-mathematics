import Mathlib
namespace C6.T4

theorem union_open {X : Type*} [TopologicalSpace X] (s t : Set X) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := hs.union ht
