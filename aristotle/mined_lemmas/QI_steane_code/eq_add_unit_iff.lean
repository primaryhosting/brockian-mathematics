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

lemma eq_add_unit_iff (i : Fin 7) (s : ZMod 2) (x y : Vec) :
    x = y + unit i s ↔ ((∀ k, k ≠ i → x k = y k) ∧ x i = y i + s) := by
  constructor
  · intro h
    subst h
    refine ⟨fun k hk => ?_, ?_⟩
    · simp [unit, hk]
    · simp [unit]
  · rintro ⟨h1, h2⟩
    funext k
    by_cases hk : k = i
    · subst hk; simpa [unit] using h2
    · simpa [unit, hk] using h1 k hk

/-- The Pauli coefficients of a `2 × 2` matrix `m`. -/
