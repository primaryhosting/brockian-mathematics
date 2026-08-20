/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

/-! ## Configuration space -/

/-- Physical three dimensional space. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The many body Coulomb energy

For `N` electrons (unit negative charge) at positions `x 0, …, x (N-1)` and `K` nuclei of
charges `z 0, …, z (K-1)` at positions `R 0, …, R (K-1)`, the classical Coulomb energy is

`W = ∑_{i<j} 1/|xᵢ - xⱼ| - ∑_{i,k} z_k/|xᵢ - R_k| + ∑_{k<l} z_k z_l/|R_k - R_l|`.

This is the potential part of the Hamiltonian appearing in the stability of matter problem. -/

theorem rpow_three_fifths_two_fifths_le (lam t d : ℝ) (hlam : 0 < lam)
    (ht : 0 ≤ t) (hd : 0 ≤ d) :
    t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5)
      ≤ (3 / 5) * (lam * t) + (2 / 5) * (lam ^ (-(3 : ℝ) / 2) * d) := by
  have hlam' : (0 : ℝ) ≤ lam := hlam.le
  have hp₁ : (0 : ℝ) ≤ lam * t := mul_nonneg hlam' ht
  have hp₂ : (0 : ℝ) ≤ lam ^ (-(3 : ℝ) / 2) * d :=
    mul_nonneg (Real.rpow_nonneg hlam' _) hd
  have key := Real.geom_mean_le_arith_mean2_weighted
    (by norm_num : (0:ℝ) ≤ 3/5) (by norm_num : (0:ℝ) ≤ 2/5) hp₁ hp₂ (by norm_num)
  have hrw : (lam * t) ^ ((3:ℝ)/5) * (lam ^ (-(3 : ℝ) / 2) * d) ^ ((2:ℝ)/5)
      = t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5) := by
    rw [Real.mul_rpow hlam' ht, Real.mul_rpow (Real.rpow_nonneg hlam' _) hd,
      ← Real.rpow_mul hlam']
    have : lam ^ ((3:ℝ)/5) * lam ^ ((-(3 : ℝ) / 2) * ((2:ℝ)/5)) = 1 := by
      rw [← Real.rpow_add hlam]
      norm_num
    calc lam ^ ((3:ℝ)/5) * t ^ ((3:ℝ)/5) * (lam ^ ((-(3 : ℝ) / 2) * ((2:ℝ)/5)) * d ^ ((2:ℝ)/5))
        = (lam ^ ((3:ℝ)/5) * lam ^ ((-(3 : ℝ) / 2) * ((2:ℝ)/5)))
            * (t ^ ((3:ℝ)/5) * d ^ ((2:ℝ)/5)) := by ring
      _ = t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5) := by rw [this, one_mul]
  rw [hrw] at key
  exact key

/-- The elementary optimisation underlying the passage from the Lieb–Thirring inequality to
stability: for `a, b > 0` and `t, d ≥ 0`,
`a t - b t^{3/5} d^{2/5} ≥ - (2/5) b (5a/(3b))^{-3/2} d`. -/
