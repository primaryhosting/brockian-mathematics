/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma geom_sum_w (a : ℕ) :
    ∑ k : Fin 10, w ^ ((k : ℕ) * a) = if 10 ∣ a then (10 : ℂ) else 0 := by
  have hz : ∀ k : Fin 10, w ^ ((k : ℕ) * a) = (w ^ a) ^ (k : ℕ) := fun k => by
    rw [← pow_mul, Nat.mul_comm]
  simp only [hz]
  rw [Fin.sum_univ_eq_sum_range (fun i => (w ^ a) ^ i) 10]
  by_cases h : 10 ∣ a
  · have hone : w ^ a = 1 := (w_pow_eq_one_iff a).mpr h
    simp [hone, h]
  · have hne : w ^ a ≠ 1 := fun hc => h ((w_pow_eq_one_iff a).mp hc)
    rw [geom_sum_eq hne, w_pow_mul_ten]
    simp [h]

