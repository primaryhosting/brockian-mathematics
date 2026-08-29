/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Steane `[[7,1,3]]` code corrects any single-qubit error

The Steane code is the CSS code built from the classical `[7,4,3]` Hamming code, whose
parity-check matrix `H` has as its `i`-th column the binary expansion of `i + 1`.  The same
matrix supplies the three `X`-type and the three `Z`-type stabilizer generators.

We work with the honest quantum state space of seven qubits, realised as the `2 ^ 7`-dimensional
complex vector space `Bits → ℂ` of amplitude functions on computational basis states
`Bits = Fin 7 → ZMod 2`, with the Hermitian form `ip f g = ∑ v, conj (f v) * g v`.
For `a b : Bits`, `pauli a b` is the Pauli operator `X(a) Z(b)` (up to an irrelevant global
sign), acting by `(pauli a b f) v = (-1) ^ (b ⬝ v) * f (v + a)`.

The code space is the joint `+1` eigenspace `IsStabilized` of the six stabilizer generators;
it is nontrivial, as witnessed by the logical `|0⟩` state `zeroL`.

The main theorem `QI.steane_code` records three facts:

1. **the code space is nonzero** (`zeroL` is a stabilizer state and `zeroL ≠ 0`);
2. **the Knill–Laflamme error-correction condition** holds for the set of all single-qubit
   Pauli errors: for codewords `f, g` and single-qubit Pauli errors `E, F`,
   `⟪E f, F g⟫ = c (E, F) * ⟪f, g⟫` with `c (E, F) = 1` if `E = F` and `0` otherwise.
   By the Knill–Laflamme theorem this is exactly the statement that the code corrects any
   single-qubit error;
3. **explicit syndrome decoding**: the decoder `decodeErr` reconstructs every single-qubit
   Pauli error from its measured syndrome.
-/

set_option maxRecDepth 40000

namespace QI

/-! ### The classical Hamming parity-check matrix -/

/-- Parity-check matrix of the classical `[7,4,3]` Hamming code: the `i`-th column is the
binary expansion of `i + 1`. -/

def IsStabilized (f : St) : Prop := ∀ k, pauli (row k) 0 f = f ∧ pauli 0 (row k) f = f

/-- The logical `|0⟩` of the Steane code: the uniform superposition of the `16` classical
Hamming codewords. -/
