import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace QI

/-! ## Setup

The Steane code is the `[[7,1,3]]` CSS code built from the classical `[7,4,3]` Hamming
code `C = ker H`, whose parity–check matrix `H` has as columns the seven nonzero
vectors of `Bit³`.

A Pauli error on `7` qubits is, up to an irrelevant global phase, described by its
symplectic (X-part, Z-part) representation: a pair of bits at every qubit.  The
error syndrome of such an error is the pair of classical Hamming syndromes of its
X-part and of its Z-part (the X-part is detected by the three Z-type stabilizer
generators and the Z-part by the three X-type generators, both given by the rows
of `H`).

"Correcting any single-qubit error" is then the statement that a decoder exists which
recovers the error *exactly* from its syndrome, for every error supported on at most
one qubit.  This is precisely non-degenerate correctability of the single-qubit error
set (the Knill–Laflamme conditions for a stabilizer code reduce to this combinatorial
statement).
-/

/-- Bits, i.e. elements of `GF(2)`. -/
abbrev Bit := ZMod 2

/-- Parity–check matrix of the classical `[7,4,3]` Hamming code: the `j`-th column is
the binary expansion of `j + 1`. -/

theorem syndrome_injOn {E F : PauliError} (hE : SingleQubit E) (hF : SingleQubit F)
    (h : syndrome E = syndrome F) : E = F := by
  obtain ⟨i, p, rfl⟩ := hE.exists_single
  obtain ⟨j, q, rfl⟩ := hF.exists_single
  exact syndrome_single_injective i j p q h

/-! ## Main theorem -/

/-- The decoder: given a syndrome, return the (unique, by `syndrome_injOn`) single-qubit
error producing it, if there is one. -/
