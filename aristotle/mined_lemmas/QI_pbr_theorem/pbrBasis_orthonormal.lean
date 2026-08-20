/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

/-! ### Two-qubit vectors, inner products and the states involved -/

/-- A (pure) qubit state vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit state vector, written in curried form. -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- The product (tensor) of two qubit vectors. -/

lemma pbrBasis_orthonormal (i j : Fin 4) :
    ip (pbrBasis i) (pbrBasis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ip, pbrBasis, Fin.sum_univ_two, Complex.ext_iff, s2_mul_s2] <;> ring_nf

/-- Antidistinguishability: the `k`-th outcome of the PBR measurement has Born
probability zero on the `k`-th of the four product states. -/
