/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the
-- header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Deutsch's algorithm

A two–qubit state is modelled as a vector of complex amplitudes indexed by the
computational basis `Bool × Bool`, i.e. a function `Bool × Bool → ℂ`, where the
first component is the query register and the second the answer register.

The algorithm is:

1. prepare `|0⟩ ⊗ |1⟩`;
2. apply a Hadamard gate to each qubit;
3. make **one** query to the oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩`;
4. apply a Hadamard gate to the first qubit;
5. measure the first qubit.

`QC.deutschProb0 f` is the probability that this measurement returns `0`; the
main theorem `QC.deutsch_correct` says that this probability is `1` when `f` is
constant and `0` when `f` is balanced, so a single query decides
constant-vs-balanced with certainty.

Remark on the suggested approach: Mathlib (as of this version) contains no
quantum-computing library — there is no `Hadamard` gate, no quantum oracle and
no notion of measurement probability — so no existing lemma states or closes
this result. The Hilbert-space and `Real.sqrt` API of Mathlib is used
throughout, but the algorithm itself is developed from scratch below.
-/

namespace QC

/-- The sign `(-1)^b` of a bit, as a complex number. -/

def oracleU (f : Bool → Bool) (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => psi (p.1, xor p.2 (f p.1))

/-- The initial state `|0⟩ ⊗ |1⟩`. -/
