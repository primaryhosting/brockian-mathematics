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

lemma huckelEigenvalue_eq (k : Fin 10) :
    ((huckelEigenvalue k : ℝ) : ℂ) = w ^ (k : ℕ) + (w ^ (k : ℕ)) ^ 9 := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 10 with ht
  have hw : w ^ (k : ℕ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h1 : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-(t : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hinv : (w ^ (k : ℕ)) ^ 9 = Complex.exp (-(t : ℂ) * Complex.I) := by
    have h2 : (w ^ (k : ℕ)) ^ 9 * Complex.exp ((t : ℂ) * Complex.I) = 1 := by
      rw [← hw, ← pow_succ]
      exact w_pow_mul_ten (k : ℕ)
    have hne : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    apply mul_right_cancel₀ hne
    rw [h2, mul_comm, h1]
  rw [hinv, hw, huckelEigenvalue, ← ht]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]

