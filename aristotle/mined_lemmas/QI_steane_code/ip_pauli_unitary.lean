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

theorem ip_pauli_unitary (a b : Vec) (f g : Vec → ℂ) :
    ip ((pauli a b).mulVec f) ((pauli a b).mulVec g) = ip f g := by
  unfold ip
  rw [sum_shift (fun x => (starRingEnd ℂ) ((pauli a b).mulVec f x)
    * ((pauli a b).mulVec g x)) a]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [pauli_mulVec, pauli_mulVec, vec_add_cancel, map_mul, chi_conj]
  calc chi (dotp b x) * (starRingEnd ℂ) (f x) * (chi (dotp b x) * g x)
      = (chi (dotp b x) * chi (dotp b x)) * ((starRingEnd ℂ) (f x) * g x) := by ring
    _ = (starRingEnd ℂ) (f x) * g x := by rw [chi_mul_self, one_mul]

/-- Distinct single-qubit Pauli errors send the code space to orthogonal subspaces:
this is what makes syndrome measurement followed by the inverse Pauli a valid recovery. -/
