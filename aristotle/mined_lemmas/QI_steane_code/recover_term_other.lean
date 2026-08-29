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

lemma recover_term_other (e e' : Fin 7 × ZMod 2 × ZMod 2) (he : e ∈ ErrIdx) (he' : e' ∈ ErrIdx)
    (hne : e' ≠ e) (f : Vec → ℂ) (hf : codeVec f) :
    (8 : ℂ)⁻¹ • ((ip ((PauliOf e').mulVec (psi 0)) ((PauliOf e).mulVec f)) • psi 0
      + (ip ((PauliOf e').mulVec (psi allOnes)) ((PauliOf e).mulVec f)) • psi allOnes) = 0 := by
  have hne' := ErrIdx_inj e' he' e he hne
  unfold PauliOf
  rw [steane_distinct_errors_orthogonal e'.1 e.1 e'.2.1 e'.2.2 e.2.1 e.2.2 hne' _ f
        ⟨1, 0, by funext x; simp [psi]⟩ hf,
      steane_distinct_errors_orthogonal e'.1 e.1 e'.2.1 e'.2.2 e.2.1 e.2.2 hne' _ f
        ⟨0, 1, by funext x; simp [psi]⟩ hf]
  simp

/-- **Explicit recovery.**  For every single-qubit Pauli error `PauliOf e` and every state
`f` of the code space, applying the recovery operation to the corrupted state returns `f`. -/
