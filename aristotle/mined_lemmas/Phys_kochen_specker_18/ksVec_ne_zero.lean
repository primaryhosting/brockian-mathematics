/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

/-! ### The 18 vectors

We use the Cabello–Estebaranz–García-Alcaine 18-vector, 9-basis Kochen–Specker set in `ℝ⁴`.
The vectors have integer coordinates, listed here as rows. -/

/-- Integer coordinates of the 18 Kochen–Specker vectors. -/

lemma ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  have hd : ∀ i : Fin 18, ksDot i i ≠ 0 := by decide
  intro h
  have h0 : inner ℝ (ksVec i) (ksVec i) = ((ksDot i i : ℤ) : ℝ) := inner_ksVec i i
  rw [h] at h0
  simp only [inner_zero_left] at h0
  exact hd i (by exact_mod_cast h0.symm)

/-! ### `{0,1}`-colorings -/

/-- A `{0,1}`-coloring (in the sense of Kochen–Specker) of the 18 vectors: no two orthogonal
vectors are both colored `1`, and in every orthogonal basis of `ℝ⁴` formed by four of the
vectors at least one is colored `1`. -/
