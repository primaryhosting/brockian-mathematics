import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem gadget_witness_inr (σ : Equiv.Perm (Vtx W)) (hσ : ∀ v, gadget W v (σ v) = 1) (s : Idx W) :
    σ (Sum.inr s) = Sum.inl s.1.2 ∨ σ (Sum.inr s) = Sum.inr s := by
  have h := hσ (Sum.inr s)
  cases hv : σ (Sum.inr s) with
  | inl j =>
    rw [hv, gadget_rl] at h
    left
    by_cases hne : s.1.2 = j
    · rw [hne]
    · rw [if_neg hne] at h; exact absurd h (by norm_num)
  | inr s' =>
    rw [hv, gadget_rr] at h
    right
    by_cases hne : s = s'
    · rw [hne]
    · rw [if_neg hne] at h; exact absurd h (by norm_num)

variable (τ : Equiv.Perm (Fin n)) (c : ∀ i, Fin (W i (τ i)))

/-- The fresh vertex used by the cycle cover associated with the permutation `τ` and the choice
function `c`. -/
