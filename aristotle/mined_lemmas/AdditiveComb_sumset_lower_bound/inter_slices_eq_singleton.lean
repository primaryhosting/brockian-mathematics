import Mathlib
-- (Lean 4 requires `import` lines to precede any module docstring, so the
-- requested header comment appears immediately below the import.)
/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Pointwise

namespace AdditiveComb

/-- The two "extremal slices" `A + {min B}` and `{max A} + B` of the sumset `A + B`
meet exactly in the single element `max A + min B`. -/

lemma inter_slices_eq_singleton {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} := by
  refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨?_, ?_⟩, ?_⟩
  · exact add_mem_add (A.max'_mem hA) (mem_singleton_self _)
  · exact add_mem_add (mem_singleton_self _) (B.min'_mem hB)
  · intro x hx
    rw [mem_inter, mem_add, mem_add] at hx
    obtain ⟨⟨a, ha, b, hb, rfl⟩, ⟨a', ha', b', hb', h⟩⟩ := hx
    rw [mem_singleton] at hb ha'
    subst hb; subst ha'
    have hmax : a ≤ A.max' hA := A.le_max' a ha
    have hmin : B.min' hB ≤ b' := B.min'_le b' hb'
    have : a = A.max' hA := le_antisymm hmax (by omega)
    rw [this]

/-- **Sumset lower bound over `ℤ`** (the Cauchy–Davenport analogue over the integers,
also the base case of Freiman's lemma): for nonempty finite sets of integers,
`|A| + |B| - 1 ≤ |A + B|`. -/
