import Mathlib
open Topology Filter
namespace C2.Topo2

theorem continuous_image_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (s : Set X) (hs : IsCompact s) : IsCompact (f '' s) :=
  hs.image hf
