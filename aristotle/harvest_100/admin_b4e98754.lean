/-
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the requested header is reproduced above as a plain block comment and
-- again below as the module docstring.)

import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

open Finset
open scoped Pointwise

/-- The sumset `A + B` of two nonempty finite sets of integers contains at least
`|A| + |B| - 1` elements (the Cauchy–Davenport analogue over `ℤ`, i.e. the base case of
Freiman's lemma).

The proof is the standard one: the sets `A + {min B}` and `{max A} + B` are both contained
in `A + B` and meet exactly in the single point `max A + min B`. -/
theorem sumset_lower_bound {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  have key : (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} := by
    refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨add_mem_add (max'_mem _ _) <|
      mem_singleton_self _, add_mem_add (mem_singleton_self _) <| min'_mem _ _⟩, ?_⟩
    simp only [mem_inter, and_imp, mem_add, mem_singleton, exists_eq_left,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, add_left_inj]
    intro a' ha' b' hb' h
    have h1 : a' ≤ A.max' hA := le_max' _ _ ha'
    have h2 : B.min' hB ≤ b' := min'_le _ _ hb'
    omega
  rw [← card_singleton_add (A.max' hA) B, ← card_add_singleton A (B.min' hB),
    ← card_union_add_card_inter, ← card_singleton (A.max' hA + B.min' hB), ← key,
    Nat.add_sub_cancel]
  exact card_mono (union_subset (add_subset_add_left <| singleton_subset_iff.2 <| min'_mem _ _) <|
    add_subset_add_right <| singleton_subset_iff.2 <| max'_mem _ _)

end AdditiveComb

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

