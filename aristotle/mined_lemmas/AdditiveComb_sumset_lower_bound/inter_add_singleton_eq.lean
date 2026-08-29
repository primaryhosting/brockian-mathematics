/-
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace AdditiveComb

open Finset Pointwise

/-- The key intersection identity: the sets `A + {min B}` and `{max A} + B` meet exactly in the
single element `max A + min B`. -/

lemma inter_add_singleton_eq (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} := by
  refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨add_mem_add (max'_mem _ _) <|
    mem_singleton_self _, add_mem_add (mem_singleton_self _) <| min'_mem _ _⟩, ?_⟩
  rintro x hx
  rw [mem_inter, mem_add, mem_add] at hx
  obtain ⟨⟨a, ha, b, hb, rfl⟩, c, hc, d, hd, hcd⟩ := hx
  rw [mem_singleton] at hb hc
  subst hb
  subst hc
  have h1 : a ≤ A.max' hA := le_max' _ _ ha
  have h2 : B.min' hB ≤ d := min'_le _ _ hd
  omega

/-- **Sumset lower bound** over the integers (the Cauchy–Davenport analogue / base case of
Freiman's lemma): for finite nonempty sets `A B` of integers,
`#A + #B - 1 ≤ #(A + B)`. -/
