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

lemma ip_pauli_unit (i j : Fin 7) (s1 t1 s2 t2 : ZMod 2) (u w : Vec)
    (hu : u = 0 ∨ u = allOnes) (hw : w = 0 ∨ w = allOnes) :
    ip ((pauli (unit i s1) (unit i t1)).mulVec (psi u))
       ((pauli (unit j s2) (unit j t2)).mulVec (psi w))
      = if unit i s1 = unit j s2 ∧ unit i t1 = unit j t2 ∧ u = w then 8 else 0 :=
  ip_pauli _ _ _ _ u w (wt_unit_add i j s1 s2) (wt_unit_add i j t1 t2) hu hw

/-- The Knill-Laflamme condition for a pair of single-qubit Pauli errors. -/
