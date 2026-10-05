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

lemma recover_term_self (e : Fin 7 × ZMod 2 × ZMod 2) (f : Vec → ℂ) (hf : codeVec f) :
    (8 : ℂ)⁻¹ • ((ip ((PauliOf e).mulVec (psi 0)) ((PauliOf e).mulVec f)) • psi 0
      + (ip ((PauliOf e).mulVec (psi allOnes)) ((PauliOf e).mulVec f)) • psi allOnes) = f := by
  unfold PauliOf
  rw [ip_pauli_unitary, ip_pauli_unitary]
  obtain ⟨α, β, rfl⟩ := hf
  rw [ip_add_right, ip_add_right, ip_smul_right, ip_smul_right, ip_smul_right, ip_smul_right,
    ip_psi 0 0 (Or.inl rfl) (Or.inl rfl), ip_psi 0 allOnes (Or.inl rfl) (Or.inr rfl),
    ip_psi allOnes 0 (Or.inr rfl) (Or.inl rfl),
    ip_psi allOnes allOnes (Or.inr rfl) (Or.inr rfl),
    if_pos rfl, if_pos rfl, if_neg zero_ne_allOnes, if_neg (Ne.symm zero_ne_allOnes)]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

