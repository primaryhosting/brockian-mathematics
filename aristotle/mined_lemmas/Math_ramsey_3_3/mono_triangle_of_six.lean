/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- An auxiliary "vector" of five booleans, read off as a function on `Fin 6` (the value at
the index `0` is irrelevant and set to `false`). -/

private theorem mono_triangle_of_six (c : Fin 6 → Fin 6 → Bool) :
    ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d := by
  obtain ⟨x, y, z, h0x, hxy₀, hyz₀, e1, e2⟩ :=
    exists_three_equal (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 0 5)
  have hx0 : x ≠ 0 := (Fin.ne_of_lt h0x).symm
  have hy0 : y ≠ 0 := (Fin.ne_of_lt (Nat.lt_trans h0x hxy₀)).symm
  have hz0 : z ≠ 0 := (Fin.ne_of_lt (Nat.lt_trans h0x (Nat.lt_trans hxy₀ hyz₀))).symm
  have hxy : x ≠ y := Fin.ne_of_lt hxy₀
  have hyz : y ≠ z := Fin.ne_of_lt hyz₀
  have hxz : x ≠ z := Fin.ne_of_lt (Nat.lt_trans hxy₀ hyz₀)
  rw [boolVec_colour c x hx0, boolVec_colour c y hy0] at e1
  rw [boolVec_colour c y hy0, boolVec_colour c z hz0] at e2
  by_cases hxy' : c x y = c 0 x
  · exact ⟨0, x, y, fun h => hx0 h.symm, fun h => hy0 h.symm, hxy, e1, hxy'.symm⟩
  · by_cases hxz' : c x z = c 0 x
    · exact ⟨0, x, z, fun h => hx0 h.symm, fun h => hz0 h.symm, hxz, e1.trans e2, hxz'.symm⟩
    · by_cases hyz' : c y z = c 0 y
      · exact ⟨0, y, z, fun h => hy0 h.symm, fun h => hz0 h.symm, hyz, e2, hyz'.symm⟩
      · refine ⟨x, y, z, hxy, hxz, hyz, ?_, ?_⟩
        · revert hxy' hxz'; cases c x y <;> cases c x z <;> cases c 0 x <;> simp
        · rw [← e1] at hyz'
          revert hxy' hyz'; cases c x y <;> cases c y z <;> cases c 0 x <;> simp

/-- The "pentagon" colouring of the edges of `K₅`: an edge is coloured `true` exactly when its
endpoints are adjacent in the 5-cycle `0 - 1 - 2 - 3 - 4 - 0`, and `false` otherwise. -/
