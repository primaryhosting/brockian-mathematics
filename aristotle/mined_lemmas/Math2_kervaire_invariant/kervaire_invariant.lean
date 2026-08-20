/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Lean requires every `import` command to come before any other command, and this file is
-- required to begin with the module docstring above; the development below is therefore
-- self-contained and uses only Lean 4 core (no imports are needed for it).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math2

/-- The dimensions in which the Kervaire invariant can be nonzero:
`2, 6, 14, 30, 62, 126`, i.e. the numbers `2 ^ j - 2` for `2 ≤ j ≤ 7`. -/

theorem kervaire_invariant
    (KervaireOne : Nat → Prop)
    (browder : ∀ n, KervaireOne n → ∃ j : Nat, 2 ≤ j ∧ n + 2 = 2 ^ j)
    (hhr : ∀ n, KervaireOne n → n ≤ 126) :
    ∀ n, KervaireOne n → KervaireDimension n := by
  intro n hn
  obtain ⟨j, hj2, hj⟩ := browder n hn
  have hle : n ≤ 126 := hhr n hn
  have h128 : (2 : Nat) ^ j ≤ 128 := by rw [← hj]; omega
  -- Hence `j ≤ 7`, since `2 ^ 8 = 256 > 128`.
  have hj7 : j ≤ 7 := by
    cases Nat.lt_or_ge j 8 with
    | inl h => omega
    | inr h =>
        have h256 : (2 : Nat) ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h
        exact absurd (Nat.le_trans h256 h128) (by decide)
  -- With `2 ≤ j ≤ 7`, the equation `n + 2 = 2 ^ j` pins `n` down to one of the six values.
  have hcases : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [KervaireDimension] <;> simp at hj <;> omega

end Math2

