import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

namespace Frontier

/-! ## Part 1: elementary finite information theory -/

/-- Kullback–Leibler divergence of `p` from `q`, over a finite alphabet.
With the `Real.log` conventions, terms with `p i = 0` contribute `0`. -/

theorem MI_nonneg {α β : Type*} [Fintype α] [Fintype β] (p : α → β → ℝ)
    (hp : ∀ x y, 0 ≤ p x y) (hs : ∑ x, ∑ y, p x y = 1) : 0 ≤ MI p := by
  set P : α × β → ℝ := fun z => p z.1 z.2 with hP
  set Q : α × β → ℝ := fun z => (∑ y', p z.1 y') * (∑ x', p x' z.2) with hQ
  have hm1 : ∑ x, (∑ y', p x y') = 1 := hs
  have hm2 : ∑ y, (∑ x', p x' y) = 1 := by rw [Finset.sum_comm]; exact hs
  have hKL := KL_nonneg P Q (fun _ => hp _ _)
    (fun _ => mul_nonneg (Finset.sum_nonneg fun _ _ => hp _ _)
      (Finset.sum_nonneg fun _ _ => hp _ _))
    (by rw [Fintype.sum_prod_type]; exact hs)
    (by
      rw [Fintype.sum_prod_type]
      simp only [hQ, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hm2]
      simpa using hm1)
    (by
      rintro ⟨x, y⟩ hne
      have hpos : 0 < p x y := lt_of_le_of_ne (hp x y) (Ne.symm hne)
      have h1 : 0 < ∑ y', p x y' :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun y' => p x y')
          (fun _ _ => hp _ _) (Finset.mem_univ y))
      have h2 : 0 < ∑ x', p x' y :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun x' => p x' y)
          (fun _ _ => hp _ _) (Finset.mem_univ x))
      exact ne_of_gt (mul_pos h1 h2))
  rw [KL, Fintype.sum_prod_type] at hKL
  exact hKL

/-- A joint distribution that factorises as a product of two probability distributions
has zero mutual information. -/
