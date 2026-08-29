import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
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

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The Hückel (adjacency) matrix of the cycle graph `C₁₆`, over `ℝ`. -/

lemma w_shift (i c k : Fin 16) :
    w ^ (((i + c : Fin 16) : ℕ) * (k : ℕ))
      = w ^ ((i : ℕ) * (k : ℕ)) * w ^ ((c : ℕ) * (k : ℕ)) := by
  rw [← pow_add]
  apply w_pow_congr
  rw [Fin.val_add]
  calc (((i : ℕ) + (c : ℕ)) % 16 * (k : ℕ)) % 16
      = (((i : ℕ) + (c : ℕ)) * (k : ℕ)) % 16 := (Nat.mod_modEq _ 16).mul_right _
    _ = ((i : ℕ) * (k : ℕ) + (c : ℕ) * (k : ℕ)) % 16 := by ring_nf

/-- The Fourier matrix diagonalizes the adjacency matrix of `C₁₆`. -/
