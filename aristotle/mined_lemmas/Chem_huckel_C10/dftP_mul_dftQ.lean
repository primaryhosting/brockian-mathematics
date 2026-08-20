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

lemma dftP_mul_dftQ : dftP * dftQ = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  simp only [dftP, dftQ, Matrix.of_apply]
  have hterm : ∀ k : Fin 10,
      w ^ ((j : ℕ) * (k : ℕ)) * ((10 : ℂ)⁻¹ * w ^ ((k : ℕ) * (10 - (l : ℕ))))
        = (10 : ℂ)⁻¹ * w ^ ((k : ℕ) * ((j : ℕ) + (10 - (l : ℕ)))) := by
    intro k
    rw [Nat.mul_add, pow_add, Nat.mul_comm (j : ℕ) (k : ℕ)]
    ring
  simp only [hterm]
  rw [← Finset.mul_sum, geom_sum_w]
  have hj := j.isLt
  have hl := l.isLt
  have hiff : (10 ∣ (j : ℕ) + (10 - (l : ℕ))) ↔ j = l := by
    rw [Fin.ext_iff]
    omega
  rw [Matrix.one_apply]
  by_cases h : j = l
  · rw [if_pos (hiff.mpr h), if_pos h]
    norm_num
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
    ring

