/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a "weight matrix" `A : V → V → ℝ`. -/

lemma bilForm_bound_norms (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ i j, A i j = A j i)
    (hlam : ∀ x : V → ℝ, (∑ i, x i = 0) → |bilForm A x x| ≤ lam * ∑ i, (x i) ^ 2)
    (x y : V → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bilForm A x y| ≤ lam * Real.sqrt (∑ i, (x i) ^ 2) * Real.sqrt (∑ i, (y i) ^ 2) := by
  set nx : ℝ := Real.sqrt (∑ i, (x i) ^ 2) with hnx
  set ny : ℝ := Real.sqrt (∑ i, (y i) ^ 2) with hny
  have hxnn : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hynn : (0 : ℝ) ≤ ∑ i, (y i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnx0 : 0 ≤ nx := Real.sqrt_nonneg _
  have hny0 : 0 ≤ ny := Real.sqrt_nonneg _
  have hnxsq : nx ^ 2 = ∑ i, (x i) ^ 2 := Real.sq_sqrt hxnn
  have hnysq : ny ^ 2 = ∑ i, (y i) ^ 2 := Real.sq_sqrt hynn
  rcases eq_or_lt_of_le hnx0 with hx0 | hxpos
  · have hzero : ∀ i, x i = 0 := by
      have hs : ∑ i, (x i) ^ 2 = 0 := by rw [← hnxsq, ← hx0]; ring
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 hs i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bilForm A x y = 0 := by
      simp only [bilForm]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [hzero i]; ring
    rw [this, ← hx0]
    simp
  rcases eq_or_lt_of_le hny0 with hy0 | hypos
  · have hzero : ∀ i, y i = 0 := by
      have hs : ∑ i, (y i) ^ 2 = 0 := by rw [← hnysq, ← hy0]; ring
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i))).1 hs i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bilForm A x y = 0 := by
      simp only [bilForm]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [hzero j]; ring
    rw [this, ← hy0]
    simp
  · have hu : ∑ i, (ny * x i) = 0 := by
      rw [← Finset.mul_sum, hx, mul_zero]
    have hv : ∑ i, (nx * y i) = 0 := by
      rw [← Finset.mul_sum, hy, mul_zero]
    have h := bilForm_bound_avg A lam hsymm hlam (fun i => ny * x i) (fun i => nx * y i) hu hv
    rw [bilForm_smul_left, bilForm_smul_right] at h
    have e1 : ∑ i, (ny * x i) ^ 2 = ny ^ 2 * nx ^ 2 := by
      rw [hnxsq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (nx * y i) ^ 2 = nx ^ 2 * ny ^ 2 := by
      rw [hnysq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at h
    rw [abs_mul, abs_mul, abs_of_nonneg hnx0, abs_of_nonneg hny0] at h
    have hprod : 0 < nx * ny := mul_pos hxpos hypos
    have h' : ny * nx * |bilForm A x y| ≤ (ny * nx) * (lam * nx * ny) := by
      calc ny * nx * |bilForm A x y| = ny * (nx * |bilForm A x y|) := by ring
        _ ≤ lam / 2 * (ny ^ 2 * nx ^ 2 + nx ^ 2 * ny ^ 2) := h
        _ = (ny * nx) * (lam * nx * ny) := by ring
    have := le_of_mul_le_mul_left (by linarith [h'] : (ny * nx) * |bilForm A x y|
      ≤ (ny * nx) * (lam * nx * ny)) (by nlinarith : (0:ℝ) < ny * nx)
    linarith [this]

/-- **Expander mixing lemma** (Alon–Chung, as presented by Wigderson).

Let `A` be a symmetric weight matrix on a finite nonempty vertex set `V` which is `d`-regular
(all row sums equal `d`), and suppose the quadratic form of `A` is bounded in absolute value by
`lam` times the squared norm on vectors orthogonal to the all-ones vector (i.e. `lam` bounds the
second eigenvalue in absolute value).  Then for all sets of vertices `S` and `T`, the
number of edges `e(S,T) = ∑_{i ∈ S} ∑_{j ∈ T} A i j` differs from its "expected" value
`d |S| |T| / n` by at most `lam * √(|S| |T|)`. -/
