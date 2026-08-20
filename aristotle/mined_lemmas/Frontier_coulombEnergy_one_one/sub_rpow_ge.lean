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

theorem sub_rpow_ge (a b t d : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) (hd : 0 ≤ d) :
    -((2 / 5) * b * ((5 * a) / (3 * b)) ^ (-(3 : ℝ) / 2) * d)
      ≤ a * t - b * (t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5)) := by
  set lam : ℝ := (5 * a) / (3 * b) with hlamdef
  have hlam : 0 < lam := by
    have : (0:ℝ) < 3 * b := by linarith
    exact div_pos (by linarith) this
  have hAMGM := rpow_three_fifths_two_fifths_le lam t d hlam ht hd
  have hmul : b * (t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5))
      ≤ b * ((3 / 5) * (lam * t) + (2 / 5) * (lam ^ (-(3 : ℝ) / 2) * d)) :=
    mul_le_mul_of_nonneg_left hAMGM hb.le
  have hcoef : b * ((3 / 5) * lam) = a := by
    rw [hlamdef]
    field_simp
  nlinarith [hmul, hcoef]

/-! ## Stability of matter -/

/-- The explicit stability constant produced by the reduction: it depends only on the
Lieb–Thirring constant `cLT`, the electrostatic constant `cB` and the screening constant
`cScr`. -/
