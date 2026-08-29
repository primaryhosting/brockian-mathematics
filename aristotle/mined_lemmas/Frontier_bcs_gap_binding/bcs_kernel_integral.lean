import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
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

namespace Frontier

/-- The BCS "kernel" integral: for a positive gap `Δ` and cutoff `ω`,
`∫_0^ω dξ / √(ξ² + Δ²) = arsinh (ω / Δ)`.

This is the standard weak-coupling BCS gap-equation integral over the shell of
single-particle energies `ξ ∈ [0, ω]` around the Fermi surface, with
quasiparticle energy `E(ξ) = √(ξ² + Δ²)`. -/

theorem bcs_kernel_integral (Δ ω : ℝ) (hΔ : 0 < Δ) :
    ∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) = Real.arsinh (ω / Δ) := by
  have hpos : ∀ x : ℝ, 0 < x ^ 2 + Δ ^ 2 := fun x =>
    add_pos_of_nonneg_of_pos (sq_nonneg x) (pow_pos hΔ 2)
  have hne : ∀ x : ℝ, Real.sqrt (x ^ 2 + Δ ^ 2) ≠ 0 := fun x =>
    Real.sqrt_ne_zero'.mpr (hpos x)
  have hcont : Continuous fun x : ℝ => 1 / Real.sqrt (x ^ 2 + Δ ^ 2) :=
    continuous_const.div ((continuous_pow 2).add continuous_const).sqrt hne
  rw [show Real.arsinh (ω / Δ) = Real.arsinh (ω / Δ) - Real.arsinh (0 / Δ) by simp]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have h1 : HasDerivAt (fun y : ℝ => y / Δ) (1 / Δ) x := by
      simpa using (hasDerivAt_id x).div_const Δ
    have h2 := (Real.hasDerivAt_arsinh (x / Δ)).comp x h1
    have hs : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
      rw [eq_div_iff hΔ.ne']
      calc Real.sqrt (1 + (x / Δ) ^ 2) * Δ
          = Real.sqrt (1 + (x / Δ) ^ 2) * Real.sqrt (Δ ^ 2) := by rw [Real.sqrt_sq hΔ.le]
        _ = Real.sqrt ((1 + (x / Δ) ^ 2) * Δ ^ 2) := (Real.sqrt_mul (by positivity) _).symm
        _ = Real.sqrt (x ^ 2 + Δ ^ 2) := by congr 1; field_simp; ring
    convert h2 using 1
    rw [hs]
    field_simp
  · exact hcont.intervalIntegrable _ _

/-- **Cooper pairing / BCS gap binding.**

For any attractive coupling `lam > 0` and any positive energy cutoff `ω`, the BCS gap
equation
`1 = lam * ∫_0^ω dξ / √(ξ² + Δ²)`
has a strictly positive solution `Δ` (the superconducting gap), namely the BCS gap
`Δ = ω / sinh (1 / lam)`.  In particular no matter how weak the attraction is, a
nonzero gap forms. -/
