import Mathlib
open Filter Topology
namespace C4.An6


theorem taylor_zeroth (f : ℝ → ℝ) (x : ℝ) (hf : Continuous f) :
    Tendsto (fun h => f (x + h)) (nhds 0) (nhds (f x)) := by
  have := (hf.tendsto (x + 0)).comp (Filter.tendsto_id.const_add x)
  simpa [Function.comp] using this

