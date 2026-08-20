import Mathlib
open Topology Filter
namespace C2.Topo2

theorem compact_closed_bounded (s : Set ℝ) (hs : IsCompact s) : IsClosed s ∧ Bornology.IsBounded s :=
  ⟨hs.isClosed, hs.isBounded⟩
