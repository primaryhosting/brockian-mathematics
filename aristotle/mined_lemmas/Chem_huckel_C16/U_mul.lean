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

theorem U_mul (m n : ℕ) : U m * U n = U (m + n) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [U, Matrix.of_apply]
  rw [Finset.sum_eq_single (⟨((i : ℕ) + m) % 16, by omega⟩ : Fin 16)]
  · have h : (((i : ℕ) + m) % 16 + n) % 16 = ((i : ℕ) + (m + n)) % 16 := by omega
    simp [h]
  · intro b _ hb
    have h : (b : ℕ) ≠ ((i : ℕ) + m) % 16 := fun h => hb (Fin.ext h)
    simp [h]
  · intro h
    simp at h

