/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- Energy cost of a single vortex of core size `a` in a 2D XY system of linear
size `R` with spin stiffness `J`:  `E = π J log (R / a)`. -/
noncomputable def vortexEnergy (J a R : ℝ) : ℝ := Real.pi * J * Real.log (R / a)

/-- Entropy of a single vortex in a 2D XY system of linear size `R` with core size
`a`: the vortex core may be placed in roughly `(R / a) ^ 2` positions, so
`S = k_B log ((R / a) ^ 2) = 2 k_B log (R / a)`. -/
noncomputable def vortexEntropy (kB a R : ℝ) : ℝ := 2 * kB * Real.log (R / a)

/-- Helmholtz free energy `F = E - T S` of a single vortex. -/
noncomputable def vortexFreeEnergy (J kB T a R : ℝ) : ℝ :=
    vortexEnergy J a R - T * vortexEntropy kB a R

/-- The Berezinskii–Kosterlitz–Thouless critical temperature `T_BKT = π J / (2 k_B)`. -/
noncomputable def bktTemp (J kB : ℝ) : ℝ := Real.pi * J / (2 * kB)

lemma vortexFreeEnergy_eq (J kB T a R : ℝ) :
    vortexFreeEnergy J kB T a R = (Real.pi * J - 2 * kB * T) * Real.log (R / a) := by
  unfold vortexFreeEnergy vortexEnergy vortexEntropy
  ring

/--
**Berezinskii–Kosterlitz–Thouless transition of the two–dimensional XY model**
(Kosterlitz–Thouless free-energy criterion for the unbinding of a single vortex).

For spin stiffness `J > 0`, Boltzmann constant `k_B > 0` and vortex core size `a > 0`,
the free energy `F(T, R) = E(R) - T S(R)` of an isolated vortex in a system of linear
size `R > a` is `(π J - 2 k_B T) log (R / a)`, which diverges logarithmically with the
system size with a temperature-dependent sign. Consequently there is a sharp critical
temperature `T_BKT = π J / (2 k_B) > 0` such that:

* for `T < T_BKT` the free energy is strictly positive and diverges to `+∞` as
  `R → ∞`: isolated vortices are suppressed and vortices remain bound in
  neutral pairs (quasi–long-range ordered phase);
* at `T = T_BKT` the free energy vanishes identically (marginality);
* for `T > T_BKT` the free energy is strictly negative and diverges to `-∞` as
  `R → ∞`: free vortices proliferate and destroy the quasi–long-range order
  (disordered phase).
-/
theorem bkt_transition (J kB a : ℝ) (hJ : 0 < J) (hkB : 0 < kB) (ha : 0 < a) :
    0 < bktTemp J kB ∧
    (∀ T R : ℝ, vortexFreeEnergy J kB T a R
        = (Real.pi * J - 2 * kB * T) * Real.log (R / a)) ∧
    (∀ T R : ℝ, a < R →
        (T < bktTemp J kB → 0 < vortexFreeEnergy J kB T a R) ∧
        (T = bktTemp J kB → vortexFreeEnergy J kB T a R = 0) ∧
        (bktTemp J kB < T → vortexFreeEnergy J kB T a R < 0)) ∧
    (∀ T : ℝ, T < bktTemp J kB →
        Filter.Tendsto (fun R : ℝ => vortexFreeEnergy J kB T a R) Filter.atTop Filter.atTop) ∧
    (∀ T : ℝ, bktTemp J kB < T →
        Filter.Tendsto (fun R : ℝ => vortexFreeEnergy J kB T a R) Filter.atTop Filter.atBot) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hsign : ∀ T : ℝ, (T < bktTemp J kB ↔ 0 < Real.pi * J - 2 * kB * T) ∧
      (T = bktTemp J kB ↔ Real.pi * J - 2 * kB * T = 0) ∧
      (bktTemp J kB < T ↔ Real.pi * J - 2 * kB * T < 0) := by
    intro T
    have h2k : (0:ℝ) < 2 * kB := by positivity
    unfold bktTemp
    refine ⟨?_, ?_, ?_⟩
    · rw [lt_div_iff₀ h2k]; constructor <;> intro h <;> nlinarith
    · rw [eq_div_iff (ne_of_gt h2k)]; constructor <;> intro h <;> nlinarith
    · rw [div_lt_iff₀ h2k]; constructor <;> intro h <;> nlinarith
  have hlogtop : Filter.Tendsto (fun R : ℝ => Real.log (R / a)) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun R : ℝ => R / a) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_div_const ha Filter.tendsto_id
    exact Real.tendsto_log_atTop.comp h1
  refine ⟨by unfold bktTemp; positivity, fun T R => vortexFreeEnergy_eq J kB T a R, ?_, ?_, ?_⟩
  · intro T R hR
    have hlog : 0 < Real.log (R / a) := by
      apply Real.log_pos
      rw [lt_div_iff₀ ha]; linarith
    rw [vortexFreeEnergy_eq]
    obtain ⟨h1, h2, h3⟩ := hsign T
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact mul_pos (h1.mp h) hlog
    · rw [h2.mp h, zero_mul]
    · exact mul_neg_of_neg_of_pos (h3.mp h) hlog
  · intro T hT
    obtain ⟨h1, _, _⟩ := hsign T
    simp only [vortexFreeEnergy_eq]
    exact Filter.Tendsto.const_mul_atTop (h1.mp hT) hlogtop
  · intro T hT
    obtain ⟨_, _, h3⟩ := hsign T
    simp only [vortexFreeEnergy_eq]
    have h : Filter.Tendsto
        (fun R : ℝ => -(-(Real.pi * J - 2 * kB * T) * Real.log (R / a))) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp
        (Filter.Tendsto.const_mul_atTop (by linarith [h3.mp hT]) hlogtop)
    have heq : (fun R : ℝ => -(-(Real.pi * J - 2 * kB * T) * Real.log (R / a)))
        = fun R : ℝ => (Real.pi * J - 2 * kB * T) * Real.log (R / a) := by
      funext R; ring
    rwa [heq] at h

end Phys

