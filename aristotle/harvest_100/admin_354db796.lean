/-
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-- The Fiedler value (algebraic connectivity) of the cycle graph `C n`. -/
noncomputable def g (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n)

/-- The spectral gap of the cycle family vanishes: `g n → 0` as `n → ∞`. -/
theorem cycle_gap_vanishes : Filter.Tendsto g Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => 2 * Real.pi / (n : ℝ)) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.div_atTop (f := fun _ : ℕ => 2 * Real.pi)
      tendsto_const_nhds tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / (n : ℝ)))
      Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp h1
  have h3 := tendsto_const_nhds (x := (2 : ℝ)) (f := Filter.atTop (α := ℕ)) |>.sub
    (h2.const_mul (2 : ℝ))
  simpa [g] using h3

end Frontier.Spectral

