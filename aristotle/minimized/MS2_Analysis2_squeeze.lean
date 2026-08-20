import Mathlib
open Filter Topology
namespace MS2.Analysis2

theorem squeeze (f g h : ℕ → ℝ) (a : ℝ) (hf : Tendsto f atTop (nhds a)) (hh : Tendsto h atTop (nhds a))
    (hfg : ∀ n, f n ≤ g n) (hgh : ∀ n, g n ≤ h n) : Tendsto g atTop (nhds a) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hf hh hfg hgh
