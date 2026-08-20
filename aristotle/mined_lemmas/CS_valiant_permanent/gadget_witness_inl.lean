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

theorem gadget_witness_inl (σ : Equiv.Perm (Vtx W)) (hσ : ∀ v, gadget W v (σ v) = 1) (i : Fin n) :
    ∃ t : Idx W, σ (Sum.inl i) = Sum.inr t ∧ t.1.1 = i := by
  have h := hσ (Sum.inl i)
  cases hv : σ (Sum.inl i) with
  | inl j => rw [hv, gadget_ll] at h; exact absurd h (by norm_num)
  | inr t =>
    refine ⟨t, rfl, ?_⟩
    rw [hv, gadget_lr] at h
    by_contra hne
    rw [if_neg hne] at h; exact absurd h (by norm_num)

/-- A fresh vertex is either traversed (and then leads to the second component of its pair) or
covered by its self-loop. -/
