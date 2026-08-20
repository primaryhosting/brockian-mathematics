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

theorem gottesman_knill (n : ℕ) :
    Fintype.card (Bits n) = 2 ^ n ∧
    Fintype.card (Pauli n) = 4 * 2 ^ n * 2 ^ n ∧
    (∀ C : Circuit n, (circuitMat C)ᴴ * circuitMat C = 1) ∧
    (∀ (C : Circuit n) (P : Pauli n),
      (circuitMat C)ᴴ * P.toMatrix * circuitMat C = (circuitConj C P).toMatrix) ∧
    (∀ (g : Gate n) (P : Pauli n) (i : Fin n), i ∉ g.support →
      (gateConj g P).x i = P.x i ∧ (gateConj g P).z i = P.z i) ∧
    (∀ g : Gate n, g.support.card ≤ 2) ∧
    (∀ (C : Circuit n) (P : Pauli n),
      ((circuitMat C)ᴴ * P.toMatrix * circuitMat C) (zeroBits n) (zeroBits n)
        = if (circuitConj C P).x = zeroBits n then iPow (circuitConj C P).k else 0) := by
  refine ⟨?_, card_pauli n, circuitMat_unitary, circuit_conj, gateConj_local,
    support_card_le_two, expectation_eq⟩
  simp

/-! ### Sanity checks: the tableau rules are the textbook Clifford conjugation rules -/

/-- `H† X H = Z`. -/
example : gateConj (Gate.H (0 : Fin 1)) ⟨0, fun _ => true, fun _ => false⟩
    = (⟨0, fun _ => false, fun _ => true⟩ : Pauli 1) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- `S† X S = -Y = i³ X Z`. -/
example : gateConj (Gate.S (0 : Fin 1)) ⟨0, fun _ => true, fun _ => false⟩
    = (⟨3, fun _ => true, fun _ => true⟩ : Pauli 1) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- `CNOT† X_c CNOT = X_c X_t`. -/
example : gateConj (Gate.CX (0 : Fin 2) 1 (by decide)) ⟨0, ![true, false], ![false, false]⟩
    = (⟨0, ![true, true], ![false, false]⟩ : Pauli 2) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- `CNOT† Z_t CNOT = Z_c Z_t`. -/
example : gateConj (Gate.CX (0 : Fin 2) 1 (by decide)) ⟨0, ![false, false], ![false, true]⟩
    = (⟨0, ![false, false], ![true, true]⟩ : Pauli 2) := by
  refine Pauli.ext (by simp [gateConj]) ?_ ?_ <;> funext i <;> fin_cases i <;>
    simp [gateConj]

/-- The simulator is a genuinely executable classical algorithm: here `X₀` is propagated
through the two-qubit circuit `H₀ · CNOT₀₁`, giving the stabilizer `Z₀ X₁` (phase `i⁰`). -/
example :
    ((circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).k,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).x 0,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).x 1,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).z 0,
      (circuitConj [Gate.H 0, Gate.CX (0 : Fin 2) 1 (by decide)]
        ⟨0, ![true, false], ![false, false]⟩).z 1)
      = (0, false, true, true, false) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;>
    simp [circuitConj, gateConj]

end QI

