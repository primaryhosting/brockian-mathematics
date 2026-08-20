import Mathlib
namespace C6.T4

theorem compact_union {X : Type*} [TopologicalSpace X] (s t : Set X) (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := hs.union ht
end C6.T4

