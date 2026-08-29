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

theorem steane_distinct_errors_orthogonal (i j : Fin 7) (s1 t1 s2 t2 : ZMod 2)
    (h : ¬(unit i s1 = unit j s2 ∧ unit i t1 = unit j t2))
    (f g : Vec → ℂ) (hf : codeVec f) (hg : codeVec g) :
    ip ((pauli (unit i s1) (unit i t1)).mulVec f)
       ((pauli (unit j s2) (unit j t2)).mulVec g) = 0 := by
  rw [ip_pauli_code i j s1 t1 s2 t2 f g hf hg, if_neg h, zero_mul]

/-! ## An explicit recovery operation -/

/-- Index set for the correctable errors: the `21` nontrivial single-qubit Paulis
together with a single copy of the identity. -/
