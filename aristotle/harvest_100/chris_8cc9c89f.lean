import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-! ## The Kosterlitz–Thouless vortex-unbinding criterion

We formalise the standard energy–entropy argument for the Berezinskii–Kosterlitz–Thouless
(BKT) topological phase transition of the two–dimensional XY model, in units where the
Boltzmann constant is `k_B = 1`.

For a 2D XY model with spin stiffness `J` on a disc of radius `R` with vortex core size `a`,
a single vortex costs energy `π J log (R / a)`, while the number of possible core positions is
`(R / a) ^ 2`, giving entropy `2 log (R / a)`.  The resulting free energy

`F = (π J - 2 T) log (R / a)`

is positive below `T_BKT = π J / 2` (isolated vortices are thermodynamically suppressed and
the vortices remain bound in neutral pairs — the quasi–long-range ordered phase) and negative
above `T_BKT` (free vortices proliferate — the disordered phase).  Exactly at `T_BKT` the free
energy vanishes; this is the transition point.  At the transition the spin-wave correlation
exponent `η(T) = T / (2 π J)` takes the universal value `1/4`.
-/

/-- Energy of a single vortex in a 2D XY model with spin stiffness `J`, in a system of
radius `R` with vortex core size `a`. -/
noncomputable def vortexEnergy (J R a : ℝ) : ℝ := Real.pi * J * Real.log (R / a)

/-- Entropy of a single vortex: the logarithm of the number `(R / a) ^ 2` of possible
positions of the vortex core (with `k_B = 1`). -/
noncomputable def vortexEntropy (R a : ℝ) : ℝ := 2 * Real.log (R / a)

/-- Free energy `F = E - T S` of a single vortex. -/
noncomputable def vortexFreeEnergy (J T R a : ℝ) : ℝ :=
  vortexEnergy J R a - T * vortexEntropy R a

/-- The Berezinskii–Kosterlitz–Thouless transition temperature `T_BKT = π J / 2`
(in units with `k_B = 1`). -/
noncomputable def TBKT (J : ℝ) : ℝ := Real.pi * J / 2

/-- The spin-wave (Gaussian) correlation exponent `η(T) = T / (2 π J)`, i.e. the exponent in
the algebraic decay `⟨s(0) · s(r)⟩ ∼ r ^ (-η)` of the low-temperature phase. -/
noncomputable def spinWaveExponent (J T : ℝ) : ℝ := T / (2 * Real.pi * J)

/-- Closed form of the single-vortex free energy. -/
lemma vortexFreeEnergy_eq (J T R a : ℝ) :
    vortexFreeEnergy J T R a = (Real.pi * J - 2 * T) * Real.log (R / a) := by
  unfold vortexFreeEnergy vortexEnergy vortexEntropy
  ring

lemma log_ratio_pos {R a : ℝ} (ha : 0 < a) (hR : a < R) : 0 < Real.log (R / a) :=
  Real.log_pos ((one_lt_div ha).mpr hR)

lemma coeff_pos_iff {J T : ℝ} : 0 < Real.pi * J - 2 * T ↔ T < TBKT J := by
  unfold TBKT
  constructor <;> intro h <;> linarith

lemma tendsto_log_ratio_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun R : ℝ => Real.log (R / a)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const ha)

/-- **The Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY model.**

For a 2D XY model with spin stiffness `J > 0`, vortex core size `a > 0` and system radius
`R > a`, the free energy of a single (unbound) vortex changes sign exactly at the transition
temperature `T_BKT = π J / 2`:

* below `T_BKT` the free energy is positive, so isolated vortices are suppressed (and diverge
  to `+∞` in the thermodynamic limit `R → ∞`): the quasi-long-range ordered phase;
* at `T_BKT` the free energy vanishes: the transition point;
* above `T_BKT` the free energy is negative, so free vortices proliferate (the free energy
  diverges to `-∞` as `R → ∞`): the disordered phase.

Moreover the spin-wave correlation exponent takes the universal Nelson–Kosterlitz value
`η(T_BKT) = 1/4` at the transition. -/
theorem bkt_transition (J T R a : ℝ) (hJ : 0 < J) (ha : 0 < a) (hR : a < R) :
    (0 < vortexFreeEnergy J T R a ↔ T < TBKT J) ∧
    (vortexFreeEnergy J T R a = 0 ↔ T = TBKT J) ∧
    (vortexFreeEnergy J T R a < 0 ↔ TBKT J < T) ∧
    (T < TBKT J →
      Filter.Tendsto (fun R' : ℝ => vortexFreeEnergy J T R' a) Filter.atTop Filter.atTop) ∧
    (TBKT J < T →
      Filter.Tendsto (fun R' : ℝ => vortexFreeEnergy J T R' a) Filter.atTop Filter.atBot) ∧
    spinWaveExponent J (TBKT J) = 1 / 4 := by
  have hL : 0 < Real.log (R / a) := log_ratio_pos ha hR
  have hF : vortexFreeEnergy J T R a = (Real.pi * J - 2 * T) * Real.log (R / a) :=
    vortexFreeEnergy_eq J T R a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF, mul_pos_iff_of_pos_right hL, coeff_pos_iff]
  · rw [hF, mul_eq_zero, or_iff_left hL.ne']
    unfold TBKT
    constructor <;> intro h <;> linarith
  · rw [hF, mul_neg_iff_of_pos_right hL]
    unfold TBKT
    constructor <;> intro h <;> linarith
  · intro hT
    have hc : 0 < Real.pi * J - 2 * T := coeff_pos_iff.mpr hT
    simpa only [vortexFreeEnergy_eq] using
      (tendsto_log_ratio_atTop ha).const_mul_atTop hc
  · intro hT
    have hc : Real.pi * J - 2 * T < 0 := by unfold TBKT at hT; linarith
    simpa only [vortexFreeEnergy_eq] using
      (tendsto_log_ratio_atTop ha).const_mul_atBot hc
  · unfold spinWaveExponent TBKT
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

end Phys

