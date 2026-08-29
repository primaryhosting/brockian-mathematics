/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring before the `import` commands.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

The state space of `7` qubits is modelled as the space of complex-valued functions on
`Vec := Fin 7 → ZMod 2`, the set of the `2^7` computational basis labels, with the
standard hermitian inner product `ip`.  Linear operators are `Matrix Vec Vec ℂ` acting
by `Matrix.mulVec`.
-/

/-- Computational basis labels for 7 qubits. -/
abbrev Vec := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form on `Vec`. -/

lemma pauli_mulVec (a b : Vec) (f : Vec → ℂ) (x : Vec) :
    (pauli a b).mulVec f x = chi (dotp b (x + a)) * f (x + a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (x + a)]
  · simp only [pauli]
    rw [if_pos (show x = x + a + a by rw [vec_add_cancel])]
  · intro y _ hy
    simp only [pauli]
    rw [if_neg (fun h => hy (by rw [h, vec_add_cancel])), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Inner products of Pauli errors applied to the two logical basis states. -/
