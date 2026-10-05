/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The hypercube and its signed adjacency operator -/

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a point of the Boolean hypercube. -/

theorem hop_hop (v : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    hop n (hop n v) x = (n : ℝ) * v x := by
  set G : Fin n × Fin n → ℝ :=
    fun p => sgn x p.1 * sgn (flipAt x p.1) p.2 * v (flipAt (flipAt x p.1) p.2) with hG
  have hdiag : ∀ i : Fin n, G (i, i) = v x := by
    intro i
    simp only [hG, sgn_flipAt_self, flipAt_flipAt_self]
    rw [sgn_mul_self, one_mul]
  have hanti : ∀ p : Fin n × Fin n, p.1 ≠ p.2 → G p + G (Prod.swap p) = 0 := by
    rintro ⟨i, j⟩ hij
    simp only [hG, Prod.swap_prod_mk] at *
    rcases lt_or_gt_of_ne hij with h | h
    · rw [sgn_flipAt_of_gt h, sgn_flipAt_of_lt h, flipAt_comm x hij]
      ring
    · rw [sgn_flipAt_of_lt h, sgn_flipAt_of_gt h, flipAt_comm x hij]
      ring
  have hexpand : hop n (hop n v) x = ∑ p : Fin n × Fin n, G p := by
    rw [hop_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hop_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [hG, mul_assoc]
  have hswap : ∑ p : Fin n × Fin n, G p = ∑ p : Fin n × Fin n, G (Prod.swap p) :=
    (Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ (fun p => rfl)).symm
  have hdouble : (2 : ℝ) * ∑ p : Fin n × Fin n, G p
      = ∑ p : Fin n × Fin n, (G p + G (Prod.swap p)) := by
    rw [Finset.sum_add_distrib, ← hswap]
    ring
  have hpoint : ∀ p : Fin n × Fin n,
      G p + G (Prod.swap p) = if p.1 = p.2 then 2 * v x else 0 := by
    rintro ⟨i, j⟩
    by_cases h : i = j
    · subst h
      simp only [Prod.swap_prod_mk, hdiag i]
      rw [if_pos trivial]
      ring
    · rw [if_neg h]
      exact hanti (i, j) h
  have hsum : ∑ p : Fin n × Fin n, (G p + G (Prod.swap p)) = 2 * ((n : ℝ) * v x) := by
    rw [Finset.sum_congr rfl fun p _ => hpoint p]
    rw [Fintype.sum_prod_type]
    have : ∀ i : Fin n, (∑ j : Fin n, if i = j then 2 * v x else 0) = 2 * v x := by
      intro i
      simp
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [Finset.sum_const]
    ring
  have := hdouble.trans hsum
  rw [hexpand]
  linarith [this]

end Frontier

