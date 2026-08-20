/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Gottesman–Knill

We formalise the Gottesman–Knill theorem: a quantum circuit built out of Clifford gates
(Hadamard, phase, CNOT) acting on `n` qubits can be simulated classically with only
`2n + 2` bits of memory and a constant amount of work per gate, in the Heisenberg picture.

The `2^n`-dimensional Hilbert space is modelled as `Bits n → ℂ`, i.e. operators are
matrices indexed by bitstrings `Bits n = Fin n → Bool`.

A Pauli operator is stored as a *tableau row* `(k, x, z)` with `k : ZMod 4` a phase
exponent and `x z : Bits n`; it denotes the operator `i^k X^x Z^z`, whose matrix is
`|b⟩ ↦ i^k (-1)^{z·b} |b ⊕ x⟩`.

The three main ingredients are:

* `QI.gateMat_unitary` : the gate matrices are unitary;
* `QI.gate_conj` : conjugating a Pauli matrix by a Clifford gate matrix is computed
  exactly by the (purely classical, bit-level) tableau update `QI.gateConj`;
* `QI.gateConj_local` : the tableau update only touches the qubits in the gate's support.

Together these give `QI.gottesman_knill`.
-/

namespace QI

/-- Bitstrings of length `n`; these index the computational basis of `n` qubits. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- Bitwise XOR of two bitstrings. -/

lemma sum_pair_support {n : ℕ} (j : Fin n) (a : Bits n) (f : Bits n → ℂ)
    (hf : ∀ c, ¬(∀ i, i ≠ j → c i = a i) → f c = 0) :
    ∑ c, f c = f (Function.update a j false) + f (Function.update a j true) := by
  have hne : Function.update a j false ≠ Function.update a j true := by
    intro h
    have := congrFun h j
    rw [Function.update_self, Function.update_self] at this
    exact Bool.noConfusion this
  rw [← Finset.sum_subset (Finset.subset_univ ({Function.update a j false,
    Function.update a j true} : Finset (Bits n)))]
  · rw [Finset.sum_pair hne]
  · intro c _ hc
    apply hf
    intro hagree
    have h1 := agree_update j a c hagree
    cases hcj : c j with
    | false =>
        have h2 : c = Function.update a j false := by rw [h1, hcj]
        exact hc (h2 ▸ Finset.mem_insert_self _ _)
    | true =>
        have h2 : c = Function.update a j true := by rw [h1, hcj]
        exact hc (h2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

