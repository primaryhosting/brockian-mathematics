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

lemma bilForm_bound_avg (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ i j, A i j = A j i)
    (hlam : ∀ x : V → ℝ, (∑ i, x i = 0) → |bilForm A x x| ≤ lam * ∑ i, (x i) ^ 2)
    (x y : V → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bilForm A x y| ≤ lam / 2 * ((∑ i, (x i) ^ 2) + ∑ i, (y i) ^ 2) := by
  have hadd : ∑ i, (x i + y i) = 0 := by
    rw [Finset.sum_add_distrib, hx, hy]; ring
  have hsub : ∑ i, (x i - y i) = 0 := by
    rw [Finset.sum_sub_distrib, hx, hy]; ring
  have h1 := hlam (fun i => x i + y i) hadd
  have h2 := hlam (fun i => x i - y i) hsub
  rw [bilForm_add_add] at h1
  rw [bilForm_sub_sub] at h2
  rw [bilForm_symm A hsymm y x] at h1 h2
  have hsq : (∑ i, (x i + y i) ^ 2) + ∑ i, (x i - y i) ^ 2
      = 2 * (∑ i, (x i) ^ 2) + 2 * ∑ i, (y i) ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : |4 * bilForm A x y| ≤ lam * (2 * (∑ i, (x i) ^ 2) + 2 * ∑ i, (y i) ^ 2) := by
    have : (4 : ℝ) * bilForm A x y =
        (bilForm A x x + bilForm A x y + bilForm A x y + bilForm A y y)
          - (bilForm A x x - bilForm A x y - bilForm A x y + bilForm A y y) := by ring
    rw [this]
    calc |(bilForm A x x + bilForm A x y + bilForm A x y + bilForm A y y)
            - (bilForm A x x - bilForm A x y - bilForm A x y + bilForm A y y)|
          ≤ |bilForm A x x + bilForm A x y + bilForm A x y + bilForm A y y|
            + |bilForm A x x - bilForm A x y - bilForm A x y + bilForm A y y| := abs_sub _ _
      _ ≤ lam * (∑ i, (x i + y i) ^ 2) + lam * ∑ i, (x i - y i) ^ 2 := add_le_add h1 h2
      _ = lam * (2 * (∑ i, (x i) ^ 2) + 2 * ∑ i, (y i) ^ 2) := by rw [← mul_add, hsq]
  rw [abs_mul] at key
  simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at key
  linarith [key]

/-- The bilinear form is bounded by `lam` times the product of the norms, on balanced vectors. -/
