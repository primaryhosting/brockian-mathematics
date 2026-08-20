/-
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`;
-- the header above is therefore a plain block comment, and is repeated as the
-- module docstring immediately after the import.)

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
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

namespace QC

open Complex

/-- The `n`-qubit quantum Fourier transform matrix, acting on the `2^n`-dimensional
state space: its `(j,k)` entry is `exp (2 π i j k / 2^n) / √(2^n)`. -/

lemma qft_apply (n : ℕ) (j k : Fin (2 ^ n)) :
    qft n j k =
      Complex.exp (2 * Real.pi * Complex.I / ((2 ^ n : ℕ) : ℂ)) ^ ((j : ℕ) * (k : ℕ)) /
        ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [qft, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
