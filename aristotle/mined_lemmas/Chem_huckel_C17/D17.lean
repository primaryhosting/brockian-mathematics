/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Matrix Polynomial

/-- A primitive 17-th root of unity. -/

noncomputable def D17 : Matrix (Fin 17) (Fin 17) ℂ :=
  Matrix.diagonal (fun k : Fin 17 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ))

/-- The adjacency matrix of the cycle graph `C₁₇`. -/
