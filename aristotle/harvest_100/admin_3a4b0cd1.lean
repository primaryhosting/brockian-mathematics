import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to come first in a file, so the header comment
-- above is placed immediately after the single `import Mathlib` line.)

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

/-! ## The Kosterlitz–Thouless vortex-unbinding argument

In the two-dimensional XY model with spin stiffness (coupling) `J > 0`, a single
vortex in a system of linear size `R` with vortex core size `a > 0` costs energy

  `E(R) = π J log (R / a)`,

while the number of distinct positions available to the vortex core is of order
`(R / a) ^ 2`, so its entropy (with `k_B = 1`) is

  `S(R) = 2 log (R / a)`.

The corresponding free energy at temperature `T` (units `k_B = 1`) is

  `F(T, R) = E(R) - T S(R) = (π J - 2 T) log (R / a)`.

Its sign changes at the Berezinskii–Kosterlitz–Thouless temperature
`T_BKT = π J / 2`: below `T_BKT` isolated vortices are suppressed (the free
energy cost diverges as `R → ∞`, so vortices bind into neutral pairs), above
`T_BKT` free vortices proliferate (the free energy diverges to `-∞`).  At the
transition the dimensionless stiffness takes the universal value
`J / T_BKT = 2 / π`. -/

/-- Energy of a single vortex of core size `a` in a 2D XY system of size `R`
with spin stiffness `J`. -/
noncomputable def vortexEnergy (J R a : ℝ) : ℝ := Real.pi * J * Real.log (R / a)

/-- Entropy of a single vortex of core size `a` in a 2D XY system of size `R`
(units `k_B = 1`): the core may sit in `~(R/a)^2` places. -/
noncomputable def vortexEntropy (R a : ℝ) : ℝ := 2 * Real.log (R / a)

/-- Free energy `E - T S` of a single vortex at temperature `T`. -/
noncomputable def vortexFreeEnergy (J T R a : ℝ) : ℝ :=
  vortexEnergy J R a - T * vortexEntropy R a

/-- The Berezinskii–Kosterlitz–Thouless critical temperature `π J / 2`. -/
noncomputable def bktTemp (J : ℝ) : ℝ := Real.pi * J / 2

lemma vortexFreeEnergy_eq (J T R a : ℝ) :
    vortexFreeEnergy J T R a = (Real.pi * J - 2 * T) * Real.log (R / a) := by
  unfold vortexFreeEnergy vortexEnergy vortexEntropy
  ring

lemma log_pos_of_lt (a R : ℝ) (ha : 0 < a) (haR : a < R) : 0 < Real.log (R / a) :=
  Real.log_pos ((one_lt_div ha).mpr haR)

lemma tendsto_log_div_atTop (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun R : ℝ => Real.log (R / a)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const ha)

end Phys

namespace Phys

/-- **The Berezinskii–Kosterlitz–Thouless transition of the 2D XY model.**

For any positive spin stiffness `J`, the single-vortex free energy
`F(T,R) = π J log(R/a) - 2 T log(R/a)` (units `k_B = 1`) undergoes a sign change
at the sharp critical temperature `T_BKT = π J / 2`:

* for `T < T_BKT` the free energy of an isolated vortex is strictly positive and
  diverges to `+∞` with the system size `R`: isolated vortices are suppressed
  and vortices are bound in neutral pairs (quasi-long-range-ordered phase);
* at `T = T_BKT` the energetic and entropic contributions cancel exactly;
* for `T > T_BKT` the free energy is strictly negative and diverges to `-∞` with
  the system size: free vortices proliferate (disordered phase).

Moreover the dimensionless stiffness at the transition takes the universal
value `J / T_BKT = 2 / π` (the Nelson–Kosterlitz universal jump), and the
critical temperature depends monotonically (indeed linearly) on `J`. -/
theorem bkt_transition (J : ℝ) (hJ : 0 < J) :
    -- sign of the vortex free energy on each side of the transition
    (∀ T R a : ℝ, 0 < a → a < R →
        (T < bktTemp J → 0 < vortexFreeEnergy J T R a) ∧
        (T = bktTemp J → vortexFreeEnergy J T R a = 0) ∧
        (bktTemp J < T → vortexFreeEnergy J T R a < 0)) ∧
      -- below the transition the cost of a free vortex diverges: vortices bind
      (∀ T a : ℝ, 0 < a → T < bktTemp J →
        Filter.Tendsto (fun R : ℝ => vortexFreeEnergy J T R a)
          Filter.atTop Filter.atTop) ∧
      -- above the transition free vortices proliferate
      (∀ T a : ℝ, 0 < a → bktTemp J < T →
        Filter.Tendsto (fun R : ℝ => vortexFreeEnergy J T R a)
          Filter.atTop Filter.atBot) ∧
      -- the transition temperature is positive and the stiffness jump is universal
      0 < bktTemp J ∧ J / bktTemp J = 2 / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hTc : bktTemp J = Real.pi * J / 2 := rfl
  have hTcpos : 0 < bktTemp J := by
    rw [hTc]; positivity
  refine ⟨?_, ?_, ?_, hTcpos, ?_⟩
  · intro T R a ha haR
    have hlog : 0 < Real.log (R / a) := log_pos_of_lt a R ha haR
    refine ⟨?_, ?_, ?_⟩
    · intro hT
      rw [vortexFreeEnergy_eq]
      have : 0 < Real.pi * J - 2 * T := by rw [hTc] at hT; linarith
      positivity
    · intro hT
      rw [vortexFreeEnergy_eq]
      have : Real.pi * J - 2 * T = 0 := by rw [hTc] at hT; linarith
      rw [this, zero_mul]
    · intro hT
      rw [vortexFreeEnergy_eq]
      have h : Real.pi * J - 2 * T < 0 := by rw [hTc] at hT; linarith
      exact mul_neg_of_neg_of_pos h hlog
  · intro T a ha hT
    have hc : 0 < Real.pi * J - 2 * T := by rw [hTc] at hT; linarith
    have := (tendsto_log_div_atTop a ha).const_mul_atTop hc
    simpa [vortexFreeEnergy_eq] using this
  · intro T a ha hT
    have hc : Real.pi * J - 2 * T < 0 := by rw [hTc] at hT; linarith
    have := (tendsto_log_div_atTop a ha).const_mul_atTop_of_neg hc
    simpa [vortexFreeEnergy_eq] using this
  · rw [hTc]
    field_simp

end Phys

