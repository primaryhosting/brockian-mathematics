/-
# Freiman Two A
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.freiman_two_A
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace AdditiveComb

open Finset
open scoped Pointwise

/-- Translates of `A` by its minimum lie in `A + A`. -/

private lemma image_add_min_subset (A : Finset ℤ) (hA : A.Nonempty) :
    A.image (· + A.min' hA) ⊆ A + A := by
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact Finset.add_mem_add ha (A.min'_mem hA)

/-- Translates of `A` by its maximum lie in `A + A`. -/
