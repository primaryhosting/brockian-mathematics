import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

open Finset Pointwise

/-- The translate `A + {min B}` and the translate `{max A} + B` meet in exactly one point,
namely `max A + min B`. -/

theorem inter_translates_eq_singleton (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} := by
  refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨add_mem_add (max'_mem _ _) <|
    mem_singleton_self _, add_mem_add (mem_singleton_self _) <| min'_mem _ _⟩, ?_⟩
  intro x hx
  rw [mem_inter] at hx
  obtain ⟨hx₁, hx₂⟩ := hx
  simp only [mem_add, mem_singleton, exists_eq_left] at hx₁ hx₂
  obtain ⟨a, ha, rfl⟩ := hx₁
  obtain ⟨b, hb, hb'⟩ := hx₂
  -- `a + min B = max A + b` with `a ≤ max A` and `min B ≤ b` forces `a = max A`.
  have ha' : a ≤ A.max' hA := le_max' _ _ ha
  have hbmin : B.min' hB ≤ b := min'_le _ _ hb
  have : a = A.max' hA := by omega
  rw [this]

/-- **Sumset lower bound** over the integers: for finite nonempty sets `A`, `B` of integers,
`|A| + |B| - 1 ≤ |A + B|` (the Cauchy–Davenport analogue over `ℤ`, i.e. the base case of
Freiman's lemma). -/
