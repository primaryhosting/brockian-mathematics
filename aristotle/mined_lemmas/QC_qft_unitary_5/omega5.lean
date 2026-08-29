import Mathlib
/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The module docstring must follow the `import` line: Lean 4 does not permit any
command, including a module doc comment, to precede the imports of a file.)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace QC

open Complex Matrix Finset

/-- A primitive 32nd root of unity, `exp (2 π i / 32)`. -/

noncomputable def omega5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 32)

/-- The 5-qubit quantum Fourier transform matrix, of size `2 ^ 5 = 32`:
`F j k = ω ^ (j * k) / √32` with `ω = exp (2 π i / 32)`. -/
