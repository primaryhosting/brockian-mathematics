/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pigeonhole for five two-valued items: among five booleans, some three of them
(at three distinct positions) are equal. -/

theorem mono_triangle_of_three_same (col : Fin 6 → Fin 6 → Bool) (p q r : Fin 6)
    (h0p : (0 : Fin 6) ≠ p) (h0q : (0 : Fin 6) ≠ q) (h0r : (0 : Fin 6) ≠ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (e1 : col 0 p = col 0 q) (e2 : col 0 q = col 0 r) :
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      col x y = col x z ∧ col x y = col y z := by
  by_cases hA : col p q = col 0 p
  · exact ⟨0, p, q, h0p, h0q, hpq, e1, hA.symm⟩
  · by_cases hB : col p r = col 0 p
    · exact ⟨0, p, r, h0p, h0r, hpr, e1.trans e2, hB.symm⟩
    · by_cases hC : col q r = col 0 p
      · exact ⟨0, q, r, h0q, h0r, hqr, e2, by rw [hC, e1]⟩
      · -- all three edges among `p`, `q`, `r` avoid the colour `col 0 p`,
        -- hence they all carry the other colour
        refine ⟨p, q, r, hpq, hpr, hqr, ?_, ?_⟩
        · cases hx : col 0 p <;> rw [hx] at hA hB <;>
            simp only [Bool.not_eq_false, Bool.not_eq_true] at hA hB <;>
            rw [hA, hB]
        · cases hx : col 0 p <;> rw [hx] at hA hC <;>
            simp only [Bool.not_eq_false, Bool.not_eq_true] at hA hC <;>
            rw [hA, hC]

/-- The pentagon (5-cycle) colouring of the edges of `K₅`: the edge `{i, j}` is
coloured `true` exactly when `i` and `j` are consecutive modulo `5`. -/
