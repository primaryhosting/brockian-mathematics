/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The shift matrices

`U n` is the matrix of the `n`-fold cyclic shift on `Fin 16`; the adjacency matrix of the
cycle graph `C₁₆` is `U 1 + U 15`. -/

/-- The matrix of the `n`-fold cyclic shift of `Fin 16`. -/

theorem lamC_eq (k : ℕ) (hk : k ≤ 16) : lamC k = zt ^ k + zt ^ (16 - k) := by
  have h1 : zt ^ (16 - k) = (zt ^ k)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact zt_pow_mul k hk)
  rw [lamC, h1, zt_pow_eq k, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

/-! ### An annihilating polynomial for the adjacency matrix -/

/-- The polynomial `∏_{k=0}^{15} (X - 2cos(2πk/16))`. -/
