/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The length of a longest chain in a finite poset. -/

theorem longestChain_mem_antichainCoverSizes :
    longestChain α ∈ antichainCoverSizes α := by
  refine ⟨(Finset.Icc 1 (longestChain α)).image (fun i => level α i), ?_, ?_, ?_⟩
  · calc ((Finset.Icc 1 (longestChain α)).image (fun i => level α i)).card
        ≤ (Finset.Icc 1 (longestChain α)).card := Finset.card_image_le
      _ = longestChain α := by simp
  · intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact level_isAntichain i
  · intro x
    refine ⟨level α (height x), Finset.mem_image.mpr ⟨height x, ?_, rfl⟩, ?_⟩
    · simp [Finset.mem_Icc, one_le_height x, height_le x]
    · simp [level]

