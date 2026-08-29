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

lemma pauli_unit_oneQubitOp (i : Fin 7) (s t : ZMod 2) :
    OneQubitOp i (pauli (unit i s) (unit i t)) := by
  refine ⟨fun p q => if p = q + s then chi (t * q) else 0, fun x y => ?_⟩
  unfold pauli
  rw [dotp_unit]
  by_cases hagree : ∀ k, k ≠ i → x k = y k
  · rw [if_pos hagree]
    show (if x = y + unit i s then chi (t * y i) else 0)
      = (if x i = y i + s then chi (t * y i) else 0)
    by_cases hi : x i = y i + s
    · rw [if_pos hi, if_pos ((eq_add_unit_iff i s x y).mpr ⟨hagree, hi⟩)]
    · rw [if_neg hi, if_neg (fun h => hi ((eq_add_unit_iff i s x y).mp h).2)]
  · rw [if_neg hagree, if_neg (fun h => hagree ((eq_add_unit_iff i s x y).mp h).1)]

/--
**The 7-qubit Steane code corrects an arbitrary single-qubit error.**

The `7`-qubit state space is `Vec → ℂ` with `Vec = Fin 7 → ZMod 2` the computational
basis labels, equipped with the hermitian inner product `ip`.  The code space is the
span of the two logical states `psi 0` and `psi allOnes`, i.e. the CSS code built from
the `[7,4,3]` Hamming code and its dual.

The first conjunct says that the two logical states are orthogonal and of equal
(nonzero) norm, so the code space is genuinely two-dimensional: it encodes one qubit.

The second conjunct is the Knill-Laflamme error-correction condition: for any two
operators `E`, `F` acting nontrivially on at most one qubit each (qubit `i` and qubit
`j` respectively), there is a *single* scalar `c`, independent of the code states, with
`⟪E f, F g⟫ = c ⟪f, g⟫` for all code vectors `f`, `g`.  By the Knill-Laflamme theorem
this is exactly the statement that the error set consisting of all single-qubit
operators is correctable, i.e. the Steane code corrects any single-qubit error.
-/
