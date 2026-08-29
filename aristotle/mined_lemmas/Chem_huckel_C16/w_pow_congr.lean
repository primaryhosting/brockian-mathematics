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

lemma w_pow_congr {a b : ℕ} (h : a % 16 = b % 16) : w ^ a = w ^ b := by
  rw [← w_pow_mod a, ← w_pow_mod b, h]

