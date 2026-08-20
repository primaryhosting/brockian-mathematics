import Mathlib
namespace C3.Topo3

/-- The intersection of a compact set with a closed set is compact. -/

theorem continuous_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (c : Y) :
    Continuous (fun _ : X => c) :=
  _root_.continuous_const

end C3.Topo3

