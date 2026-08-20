/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

/-! ## Basic vector algebra in `ℝ³` -/

/-- Euclidean three-space, as a triple of reals. -/
abbrev R3 := ℝ × ℝ × ℝ

/-- The standard inner product on `ℝ³`. -/

lemma two_le_ratio_eq_iff {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * (r * Real.sqrt (R ^ 2 - r ^ 2)) = R ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hs_sq : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := sq_sqrt_sq_sub hr hR
  have hs_nonneg : 0 ≤ Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_nonneg _
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2nonneg : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · intro h
    have hsr : Real.sqrt (R ^ 2 - r ^ 2) = r := by nlinarith [sq_nonneg (r - Real.sqrt (R ^ 2 - r ^ 2))]
    have hR2 : R ^ 2 = 2 * r ^ 2 := by nlinarith
    have hRpos : 0 < R := lt_trans hr hR
    have hRe : R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hRpos.le).symm
    rw [hRe, hR2, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hr.le]
  · intro h
    subst h
    have hRr : Real.sqrt 2 * r * (Real.sqrt 2 * r) = 2 * r ^ 2 := by nlinarith
    have : (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 := by nlinarith
    rw [this, Real.sqrt_sq hr.le]
    nlinarith

/-! ## Main results -/

/-- **The Willmore conjecture for tori of revolution** (Willmore, 1965): the base case of the
Willmore conjecture, which was proved in full generality for immersed genus-one surfaces by
Marques and Neves.

Every torus of revolution in `ℝ³` (with radii `R > r > 0`) has Willmore energy
`∫ H² dA ≥ 2π²`, and the bound is attained exactly by the *Clifford tori*, those with
`R = √2 · r`.

The statement is packaged as: (i) the universal lower bound `2π²`; (ii) attainment by the
Clifford torus; (iii) the characterisation of the equality case. -/
