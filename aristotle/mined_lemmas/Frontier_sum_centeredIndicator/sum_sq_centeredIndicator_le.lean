import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "centered indicator" of a finite set `S`: the indicator of `S` minus its mean value.
It is orthogonal to the all-ones vector. -/

lemma sum_sq_centeredIndicator_le (hV : (Fintype.card V) ≠ 0) (S : Finset V) :
    ∑ i, (centeredIndicator S i) ^ 2 ≤ (S.card : ℝ) := by
  rw [sum_sq_centeredIndicator hV S]
  have hn : (0:ℝ) < (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
    exact_mod_cast this
  have : (0:ℝ) ≤ (S.card : ℝ) ^ 2 / (Fintype.card V) := by positivity
  linarith

/-- Expansion of the bilinear form of `A` on the centered indicators of `S` and `T`,
for a matrix with all row sums and all column sums equal to `d`. -/
