/-!
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

/-!
## The Berezinskii–Kosterlitz–Thouless transition of the 2D XY model

We formalise the Kosterlitz–Thouless *energy–entropy* criterion, which is the
mathematical content identifying the BKT topological phase transition.

For the two-dimensional XY model with spin stiffness (coupling) `J`, a single
unit-charge vortex centred in a box of linear size `L`, with a core cut off at
radius `a`, has phase gradient of modulus `|∇θ(r)| = 1/r`, hence spin-wave energy
density `(J/2)|∇θ|² = (J/2)(1/r)²`.  Integrating this over the annulus
`a ≤ r ≤ L` (area element `2πr dr`) gives the logarithmically divergent vortex
energy `E = πJ log (L/a)`.

The vortex core may sit at any of `(L/a)²` distinguishable positions, so its
entropy (in units of `k_B`) is `S = log ((L/a)²) = 2 log (L/a)`.

The free energy of a single free vortex is therefore
`F = E - T S = (πJ - 2T) log (L/a)`,
whose sign changes at the *BKT temperature* `T_BKT = πJ/2` (with `k_B = 1`).

* For `T < T_BKT` we have `F > 0`: isolated vortices are thermodynamically
  suppressed, they occur only in bound vortex–antivortex pairs, and the system is
  in the quasi-long-range-ordered (topologically ordered) phase.
* For `T > T_BKT` we have `F < 0`: free vortices proliferate, unbinding destroys
  the quasi-long-range order, and the system is disordered.
* At `T = T_BKT` the free energy vanishes; `T_BKT` is the unique such
  temperature, and there the stiffness-to-temperature ratio takes the universal
  value `J / T_BKT = 2/π` (the universal jump of the superfluid stiffness).
-/

/-- Radial energy profile of a single unit-charge vortex of the 2D XY model with
spin stiffness `J`: the spin-wave energy density `(J/2)|∇θ|² = (J/2)(1/r)²`
multiplied by the circumference `2πr` of the circle of radius `r`. -/
noncomputable def vortexEnergyDensity (J r : ℝ) : ℝ := (J / 2) * (1 / r) ^ 2 * (2 * Real.pi * r)

/-- Energy of a single vortex in a box of linear size `L` with core radius `a`. -/
noncomputable def vortexEnergy (J a L : ℝ) : ℝ := Real.pi * J * Real.log (L / a)

/-- Number of distinguishable positions for the vortex core in the box. -/
noncomputable def vortexPositions (a L : ℝ) : ℝ := (L / a) ^ 2

/-- Entropy of a single vortex, in units of Boltzmann's constant. -/
noncomputable def vortexEntropy (a L : ℝ) : ℝ := Real.log (vortexPositions a L)

/-- Helmholtz free energy `F = E - T S` of a single free vortex. -/
noncomputable def vortexFreeEnergy (J T a L : ℝ) : ℝ :=
  vortexEnergy J a L - T * vortexEntropy a L

/-- The Berezinskii–Kosterlitz–Thouless transition temperature (units `k_B = 1`). -/
noncomputable def T_BKT (J : ℝ) : ℝ := Real.pi * J / 2

/-- The vortex energy is the integral of the spin-wave energy density over the
annulus `a ≤ r ≤ L`, and it diverges logarithmically in the system size. -/
theorem vortexEnergy_eq_integral (J a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    (∫ r in a..L, vortexEnergyDensity J r) = vortexEnergy J a L := by
  have hcongr : ∀ r ∈ Set.uIcc a L, vortexEnergyDensity J r = (Real.pi * J) * (1 / r) := by
    intro r hr
    have hr0 : r ≠ 0 := by
      rcases Set.mem_uIcc.mp hr with h | h
      · exact ne_of_gt (lt_of_lt_of_le ha h.1)
      · exact ne_of_gt (lt_of_lt_of_le hL h.1)
    unfold vortexEnergyDensity
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_one_div_of_pos ha hL]
  rfl

/-- The vortex entropy is `2 log (L/a)`. -/
theorem vortexEntropy_eq (a L : ℝ) : vortexEntropy a L = 2 * Real.log (L / a) := by
  unfold vortexEntropy vortexPositions
  rw [Real.log_pow]
  norm_num

/-- Explicit form of the single-vortex free energy: `F = (πJ - 2T) log (L/a)`. -/
theorem vortexFreeEnergy_eq (J T a L : ℝ) :
    vortexFreeEnergy J T a L = (Real.pi * J - 2 * T) * Real.log (L / a) := by
  unfold vortexFreeEnergy vortexEnergy
  rw [vortexEntropy_eq]
  ring

/-- **Berezinskii–Kosterlitz–Thouless transition of the two-dimensional XY model.**

For a 2D XY model with spin stiffness `J > 0`, vortex core radius `a > 0` and
system size `L > a`, the Kosterlitz–Thouless energy–entropy analysis of a single
free vortex yields, with `k_B = 1`:

1. the vortex energy is the integral of the spin-wave energy density `(J/2)|∇θ|²`
   over the annulus `a ≤ r ≤ L`, equal to `πJ log (L/a)`;
2. the vortex entropy is `log ((L/a)²) = 2 log (L/a)`, and both energy and entropy
   diverge logarithmically with the system size;
3. the free energy is `F = (πJ - 2T) log (L/a)`, a strictly decreasing function of
   the temperature;
4. **ordered (topological) phase**: for `T < T_BKT = πJ/2` one has `F > 0`, so
   isolated vortices are suppressed (vortices are bound in pairs);
5. **critical point**: `F = 0` exactly at `T = T_BKT`, and at no other temperature;
6. **disordered phase**: for `T > T_BKT` one has `F < 0`, so free vortices
   proliferate and unbind;
7. at the transition the stiffness-to-temperature ratio takes the universal value
   `J / T_BKT = 2/π`.
-/
theorem bkt_transition (J a L : ℝ) (hJ : 0 < J) (ha : 0 < a) (haL : a < L) :
    -- (1) vortex energy from the spin-wave energy density
    (∫ r in a..L, vortexEnergyDensity J r) = vortexEnergy J a L ∧
    vortexEnergy J a L = Real.pi * J * Real.log (L / a) ∧
    -- (2) vortex entropy from counting core positions
    vortexEntropy a L = 2 * Real.log (L / a) ∧
    0 < Real.log (L / a) ∧
    -- (3) explicit free energy, strictly decreasing in the temperature
    (∀ T : ℝ, vortexFreeEnergy J T a L = (Real.pi * J - 2 * T) * Real.log (L / a)) ∧
    StrictAnti (fun T : ℝ => vortexFreeEnergy J T a L) ∧
    -- (4) below the transition: single vortices are suppressed
    (∀ T : ℝ, T < T_BKT J → 0 < vortexFreeEnergy J T a L) ∧
    -- (5) the transition point is the unique zero of the free energy
    (∀ T : ℝ, vortexFreeEnergy J T a L = 0 ↔ T = T_BKT J) ∧
    -- (6) above the transition: free vortices proliferate
    (∀ T : ℝ, T_BKT J < T → vortexFreeEnergy J T a L < 0) ∧
    -- (7) universal ratio at the transition
    0 < T_BKT J ∧ J / T_BKT J = 2 / Real.pi := by
  have hL : 0 < L := lt_trans ha haL
  have hlog : 0 < Real.log (L / a) := Real.log_pos (by rw [lt_div_iff₀ ha]; linarith)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hTc : 0 < T_BKT J := by
    unfold T_BKT; positivity
  refine ⟨vortexEnergy_eq_integral J a L ha hL, rfl, vortexEntropy_eq a L, hlog,
    fun T => vortexFreeEnergy_eq J T a L, ?_, ?_, ?_, ?_, hTc, ?_⟩
  · intro T₁ T₂ h
    simp only [vortexFreeEnergy_eq]
    have : (Real.pi * J - 2 * T₂) < (Real.pi * J - 2 * T₁) := by linarith
    exact (mul_lt_mul_right hlog).mpr this
  · intro T hT
    rw [vortexFreeEnergy_eq]
    have : 0 < Real.pi * J - 2 * T := by unfold T_BKT at hT; linarith
    positivity
  · intro T
    rw [vortexFreeEnergy_eq, mul_eq_zero]
    constructor
    · rintro (h | h)
      · unfold T_BKT; linarith
      · exact absurd h (ne_of_gt hlog)
    · intro h
      left
      unfold T_BKT at h
      linarith
  · intro T hT
    rw [vortexFreeEnergy_eq]
    have h1 : Real.pi * J - 2 * T < 0 := by unfold T_BKT at hT; linarith
    exact mul_neg_of_neg_of_pos h1 hlog
  · unfold T_BKT
    field_simp

end Phys

