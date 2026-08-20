import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 15-th root of unity. -/

lemma zeta_add_neg (k : Fin 15) :
    zeta k + zeta (-k) = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 15 with ht
  have h1 : zeta k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [zeta, om, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hmul : zeta k * zeta (-k) = 1 := by
    rw [← zeta_add]
    simp [zeta_zero]
  have h2 : zeta (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have hk : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hmul' : Complex.exp ((t : ℂ) * Complex.I) * zeta (-k) = 1 := by rw [← h1]; exact hmul
    rw [Complex.exp_neg]
    field_simp
    linear_combination hmul'
  rw [h1, h2, ← neg_mul]
  have hc := Complex.two_cos ((t : ℂ))
  push_cast
  linear_combination -hc

/-- The adjacency matrix of the cycle graph `C₁₅`. -/
