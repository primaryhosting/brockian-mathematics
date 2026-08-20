import Mathlib
open Topology Filter
namespace C2.Topo2

theorem connected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (s : Set X) (hs : IsConnected s) : IsConnected (f '' s) :=
  hs.image f hf.continuousOn
end C2.Topo2

