/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

set_option grind.warning false

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

lemma hasSum_logistic_series {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => (-1:ℝ)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y)))) (y * logistic y) := by
  set q := Real.exp (-y/2) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hgeom : HasSum (fun n : ℕ => (-q)^n) (1 - (-q))⁻¹ := by
    apply hasSum_geometric_of_norm_lt_one
    rw [norm_neg, Real.norm_of_nonneg hq0.le]; exact hq1
  have hsum := hgeom.mul_left (y * q)
  have hfun : (fun n : ℕ => (-1:ℝ)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y))))
      = fun n : ℕ => y * q * (-q)^n := by
    funext n
    have harg : (n:ℝ) * (-y/2) + (-y/2) = -(((n:ℝ)+1)/2 * y) := by ring
    calc (-1:ℝ)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y)))
        = (-1:ℝ)^n * (y * Real.exp ((n:ℝ) * (-y/2) + (-y/2))) := by rw [harg]
      _ = y * q * (-q)^n := by
          rw [Real.exp_add, Real.exp_nat_mul, neg_pow, ← hq]; ring
  have hval : y * q * (1 - (-q))⁻¹ = y * logistic y := by
    have he : Real.exp (y/2) = q⁻¹ := by
      rw [hq, ← Real.exp_neg]; congr 1; ring
    unfold logistic
    rw [he, sub_neg_eq_add]
    field_simp
    ring
  rw [hfun, ← hval]
  exact hsum

