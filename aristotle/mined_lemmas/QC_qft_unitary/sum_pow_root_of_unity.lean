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

lemma sum_pow_root_of_unity (N : ℕ) (x : ℂ) (hx : x ^ N = 1) :
    ∑ m ∈ Finset.range N, x ^ m = if x = 1 then (N : ℂ) else 0 := by
  by_cases h : x = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hx, sub_self, zero_div]

/-- The entries of the QFT matrix, written in terms of the primitive root of unity
`ζ = exp (2 π i / 2^n)`. -/
