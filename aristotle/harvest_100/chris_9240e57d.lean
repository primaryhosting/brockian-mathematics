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
noncomputable def vortexEnergy (J L a : ℝ) : ℝ := Real.pi * J * Real.log (L / a)

/-- Entropy of a single vortex: its core may be placed in roughly `(L / a) ^ 2`
distinct positions, so `S = k_B log ((L / a) ^ 2) = 2 k_B log (L / a)`. -/
noncomputable def vortexEntropy (kB L a : ℝ) : ℝ := 2 * kB * Real.log (L / a)

/-- Helmholtz free energy of a single vortex, `F = E - T S`. -/
noncomputable def vortexFreeEnergy (J kB T L a : ℝ) : ℝ :=
  vortexEnergy J L a - T * vortexEntropy kB L a

/-- The Berezinskii–Kosterlitz–Thouless transition temperature `T_BKT = π J / (2 k_B)`. -/
noncomputable def bktTemperature (J kB : ℝ) : ℝ := Real.pi * J / (2 * kB)

lemma vortexFreeEnergy_eq (J kB T L a : ℝ) :
    vortexFreeEnergy J kB T L a = (Real.pi * J - 2 * kB * T) * Real.log (L / a) := by
  unfold vortexFreeEnergy vortexEnergy vortexEntropy
  ring

lemma log_ratio_pos {L a : ℝ} (ha : 0 < a) (hL : a < L) : 0 < Real.log (L / a) := by
  apply Real.log_pos
  rw [lt_div_iff₀ ha]
  simpa using hL

/-- For positive spin stiffness and positive Boltzmann constant the BKT temperature
is positive. -/
lemma bktTemperature_pos {J kB : ℝ} (hJ : 0 < J) (hkB : 0 < kB) :
    0 < bktTemperature J kB := by
  unfold bktTemperature
  positivity

/-- **Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model.**

For a single vortex in a sample of linear size `L` with core size `a < L`, the free
energy `F = E - T S`, with `E = π J log (L / a)` the vortex energy and
`S = 2 k_B log (L / a)` its positional entropy, changes sign exactly at the
BKT temperature `T_BKT = π J / (2 k_B)`:

* below `T_BKT` the free energy of an isolated vortex is positive and diverges as
  `L → ∞`, so free vortices are suppressed and the system is in the quasi-long-range
  ordered (bound vortex–antivortex) phase;
* at `T_BKT` the free energy vanishes identically;
* above `T_BKT` the free energy is negative and diverges to `-∞` as `L → ∞`, so free
  vortices proliferate and destroy the quasi-long-range order.

The divergence in `L` is recorded by the fact that the free energy is the sign-fixed
coefficient `π J - 2 k_B T` times `log (L / a) → ∞`. -/
theorem bkt_transition {J kB T L a : ℝ} (hkB : 0 < kB)
    (ha : 0 < a) (hL : a < L) :
    (T < bktTemperature J kB → 0 < vortexFreeEnergy J kB T L a) ∧
    (T = bktTemperature J kB → vortexFreeEnergy J kB T L a = 0) ∧
    (bktTemperature J kB < T → vortexFreeEnergy J kB T L a < 0) := by
  have hlog : 0 < Real.log (L / a) := log_ratio_pos ha hL
  have hkey : ∀ T' : ℝ, (T' < bktTemperature J kB ↔ 0 < Real.pi * J - 2 * kB * T') := by
    intro T'
    rw [bktTemperature, lt_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [vortexFreeEnergy_eq]
    exact mul_pos ((hkey T).mp h) hlog
  · rw [vortexFreeEnergy_eq, h, bktTemperature]
    have : Real.pi * J - 2 * kB * (Real.pi * J / (2 * kB)) = 0 := by
      field_simp
      ring
    rw [this, zero_mul]
  · rw [vortexFreeEnergy_eq]
    have hneg : Real.pi * J - 2 * kB * T < 0 := by
      by_contra hc
      push_neg at hc
      rcases lt_or_eq_of_le hc with hc' | hc'
      · exact absurd ((hkey T).mpr hc') (not_lt.mpr h.le)
      · rw [bktTemperature, div_lt_iff₀ (by positivity)] at h
        nlinarith
    exact mul_neg_of_neg_of_pos hneg hlog

/-- In the low-temperature phase the isolated-vortex free energy diverges to `+∞`
with the system size, confirming that free vortices are entropically forbidden. -/
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
theorem bkt_highT_free_energy_tendsto_atBot {J kB T a : ℝ} (hkB : 0 < kB) (ha : 0 < a)
    (hT : bktTemperature J kB < T) :
    Filter.Tendsto (fun L : ℝ => vortexFreeEnergy J kB T L a) Filter.atTop Filter.atBot := by
  have hc : Real.pi * J - 2 * kB * T < 0 := by
    rw [bktTemperature, div_lt_iff₀ (by positivity)] at hT
    nlinarith
  have h1 : Filter.Tendsto (fun L : ℝ => Real.log (L / a)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const ha)
  simp only [vortexFreeEnergy_eq]
  exact Filter.Tendsto.const_mul_atTop_of_neg hc h1

end Phys

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

