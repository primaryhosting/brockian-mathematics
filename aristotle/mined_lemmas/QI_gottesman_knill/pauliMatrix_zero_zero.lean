/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

lemma pauliMatrix_zero_zero {n : ℕ} (p : Pauli n) :
    pauliMatrix p 0 0 = if p.x = 0 then ph p.s else 0 := by
  rw [pauliMatrix_apply]
  by_cases h : p.x = 0
  · rw [if_pos h, if_pos (by rw [h]; simp), ip_zero_right, psign_zero, mul_one]
  · have hcond : ¬ ((0 : Bits n) = 0 + p.x) := by
      simp only [zero_add]
      exact fun hh => h hh.symm
    rw [if_neg hcond, if_neg h, mul_zero]

/-! ## Gottesman–Knill -/

/--
**Gottesman–Knill.** Stabilizer (Clifford) circuits are efficiently classically simulable.

For every circuit `gs` built from the Clifford generators `H`, `S`, `CZ` on `n` qubits and every
Pauli operator `p` (given by its classical tableau data: a phase in `ZMod 4` and `X`/`Z`
exponent vectors):

1. the circuit matrix `circuitMatrix gs` is unitary;
2. *(correctness of the classical simulation)* Heisenberg evolution of `p` by the circuit is
   exactly the Pauli operator whose tableau is computed by the purely classical function
   `simulate gs p`, i.e. `U P U† = pauliMatrix (simulate gs p)`;
3. *(classical readout)* the resulting expectation value in the all-zeros computational basis
   state `|0…0⟩` is read off directly from the simulated tableau;
4. *(efficiency)* the classical cost of the simulation — the number of tableau entries written
   while updating all `2n` rows of a stabilizer tableau along the circuit — is at most
   `6 * n * gs.length`, i.e. linear in the number of qubits and in the circuit size;
5. *(locality)* each gate update only writes to the qubit positions in the gate's support,
   which has at most two elements.
-/
