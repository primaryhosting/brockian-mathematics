/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Math


theorem ramsey6 (c : Sym2 (Fin 6) → Bool) :
    ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      c s(a, b) = c s(a, d) ∧ c s(a, d) = c s(b, d) := by
  have h := key (c s(0,1)) (c s(0,2)) (c s(0,3)) (c s(0,4)) (c s(0,5)) (c s(1,2)) (c s(1,3)) (c s(1,4)) (c s(1,5)) (c s(2,3)) (c s(2,4)) (c s(2,5)) (c s(3,4)) (c s(3,5)) (c s(4,5))
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨0, 1, 2, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 1, 3, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 1, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 1, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 2, 3, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 2, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 2, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨0, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 2, 3, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 2, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 2, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨1, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨2, 3, 4, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨2, 3, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨2, 4, 5, by decide, by decide, by decide, h.1, h.2⟩
  · exact ⟨3, 4, 5, by decide, by decide, by decide, h.1, h.2⟩

/-- The "pentagon" 2-coloring of the edges of `K₅`: an edge is coloured `true`
exactly when its endpoints are consecutive modulo `5`. -/
