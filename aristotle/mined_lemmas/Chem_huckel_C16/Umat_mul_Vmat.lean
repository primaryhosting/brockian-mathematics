/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import commands, so the required
header appears here as an ordinary block comment; the text is otherwise verbatim.)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₆`, i.e. the Hückel matrix of
cyclic C₁₆ in units where the Coulomb integral is `0` and the resonance integral is `1`. -/

theorem Umat_mul_Vmat : Umat * Vmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 16, Umat i k * Vmat k j = (16 : ℂ)⁻¹ * echar (k * (i - j)) := by
    intro k
    have h1 : echar (i * k) = echar (k * (i - j)) * echar (k * j) := by
      rw [← echar_add]
      congr 1
      rw [← mul_add, sub_add_cancel, mul_comm]
    simp only [Umat, Vmat, Matrix.of_apply, h1]
    rw [mul_comm ((16 : ℂ)⁻¹), ← mul_assoc, mul_assoc _ (echar (k * j)),
      mul_inv_cancel₀ (echar_ne_zero _), mul_one, mul_comm]
  simp only [key, ← Finset.mul_sum, echar_sum, Matrix.one_apply, sub_eq_zero]
  split <;> norm_num

