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

theorem isPrimitiveRoot_omega5 : IsPrimitiveRoot omega5 32 := by
  have h := Complex.isPrimitiveRoot_exp 32 (by norm_num)
  simpa [omega5] using h

