/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- Energy cost of a single vortex in a 2D XY model with spin stiffness `J`, in a
square sample of linear size `L` with short-distance (core) cutoff `a`:
`E = π J log (L / a)`. -/

theorem bkt_lowT_free_energy_tendsto_atTop {J kB T a : ℝ} (hkB : 0 < kB) (ha : 0 < a)
    (hT : T < bktTemperature J kB) :
    Filter.Tendsto (fun L : ℝ => vortexFreeEnergy J kB T L a) Filter.atTop Filter.atTop := by
  have hc : 0 < Real.pi * J - 2 * kB * T := by
    rw [bktTemperature, lt_div_iff₀ (by positivity)] at hT
    nlinarith
  have h1 : Filter.Tendsto (fun L : ℝ => Real.log (L / a)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const ha)
  simp only [vortexFreeEnergy_eq]
  exact Filter.Tendsto.const_mul_atTop hc h1

/-- In the high-temperature phase the isolated-vortex free energy diverges to `-∞`
with the system size: free vortices proliferate. -/
