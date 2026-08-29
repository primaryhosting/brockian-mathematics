import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

section

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a weight matrix `A`. -/

lemma bil_le_sqrt {A : V → V → ℝ} {lam : ℝ} (hsymm : ∀ i j, A i j = A j i) (hlam0 : 0 ≤ lam)
    (hlam : ∀ z : V → ℝ, ∑ i, z i = 0 → |bil A z z| ≤ lam * qf z)
    (x y : V → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bil A x y| ≤ lam * Real.sqrt (qf x) * Real.sqrt (qf y) := by
  rcases eq_or_lt_of_le (qf_nonneg x) with hx0 | hx0
  · have hxz : ∀ i, x i = 0 := (qf_eq_zero_iff x).1 hx0.symm
    have hb0 : bil A x y = 0 := by
      simp only [bil, hxz, zero_mul, Finset.sum_const_zero]
    rw [hb0, ← hx0]
    simp
  rcases eq_or_lt_of_le (qf_nonneg y) with hy0 | hy0
  · have hyz : ∀ i, y i = 0 := (qf_eq_zero_iff y).1 hy0.symm
    have hb0 : bil A x y = 0 := by
      simp only [bil, hyz, mul_zero, Finset.sum_const_zero]
    rw [hb0, ← hy0]
    simp
  have hapos : 0 < Real.sqrt (qf x) := Real.sqrt_pos.2 hx0
  have hbpos : 0 < Real.sqrt (qf y) := Real.sqrt_pos.2 hy0
  have ha2 : Real.sqrt (qf x) ^ 2 = qf x := Real.sq_sqrt hx0.le
  have hb2 : Real.sqrt (qf y) ^ 2 = qf y := Real.sq_sqrt hy0.le
  have htpos : 0 < Real.sqrt (qf y) / Real.sqrt (qf x) := div_pos hbpos hapos
  have hsx : ∑ i, (Real.sqrt (qf y) / Real.sqrt (qf x)) * x i = 0 := by
    rw [← Finset.mul_sum, hx, mul_zero]
  have key := bil_le_half hsymm hlam
    (fun i => (Real.sqrt (qf y) / Real.sqrt (qf x)) * x i) y hsx hy
  rw [bil_smul_left, qf_smul, abs_mul, abs_of_pos htpos] at key
  have ht2 : (Real.sqrt (qf y) / Real.sqrt (qf x)) ^ 2 * qf x = qf y := by
    rw [div_pow, ha2, hb2]
    field_simp
  rw [ht2] at key
  have hstep : Real.sqrt (qf y) / Real.sqrt (qf x) * |bil A x y| ≤ lam * qf y := by
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hapos] at hstep
  have hfinal : |bil A x y| ≤ lam * Real.sqrt (qf x) * Real.sqrt (qf y) := by
    have hmul : Real.sqrt (qf y) * Real.sqrt (qf y) = qf y := Real.mul_self_sqrt hy0.le
    have h' : Real.sqrt (qf y) * |bil A x y|
        ≤ Real.sqrt (qf y) * (lam * Real.sqrt (qf x) * Real.sqrt (qf y)) := by
      calc Real.sqrt (qf y) * |bil A x y| ≤ lam * qf y * Real.sqrt (qf x) := hstep
        _ = Real.sqrt (qf y) * (lam * Real.sqrt (qf x) * Real.sqrt (qf y)) := by
            rw [← hmul]; ring
    exact le_of_mul_le_mul_left h' hbpos
  exact hfinal

/-! ### Indicator vectors -/

