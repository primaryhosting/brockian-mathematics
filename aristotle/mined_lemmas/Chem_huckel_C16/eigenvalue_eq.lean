import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
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

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The Hückel (adjacency) matrix of the cycle graph `C₁₆`, over `ℝ`. -/

lemma eigenvalue_eq (k : Fin 16) :
    w ^ (k : ℕ) + w ^ (15 * (k : ℕ)) = (huckelEigenvalue k : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 16 with ht
  have hwk : w ^ (k : ℕ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hmul : w ^ (k : ℕ) * w ^ (15 * (k : ℕ)) = 1 := by
    rw [← pow_add]
    have h16 : (k : ℕ) + 15 * (k : ℕ) = 16 * (k : ℕ) := by ring
    rw [h16, pow_mul, w_pow_16, one_pow]
  have hne : w ^ (k : ℕ) ≠ 0 := by
    rw [hwk]; exact Complex.exp_ne_zero _
  have hinv : w ^ (15 * (k : ℕ)) = Complex.exp (-(t : ℂ) * Complex.I) := by
    have hQ : w ^ (15 * (k : ℕ)) = (w ^ (k : ℕ))⁻¹ := by
      field_simp at hmul ⊢
      linear_combination hmul
    rw [hQ, hwk, ← Complex.exp_neg]
    ring_nf
  rw [hwk, hinv, ← Complex.two_cos, huckelEigenvalue, ← ht]
  push_cast
  ring

