import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace QI

/-- Bit strings of length `n`, as vectors over the field `ZMod 2`.
Addition is bitwise XOR. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟨x, y⟩ = ⨁ i, x i * y i`. -/

theorem patch_shift {n : ℕ} {Q : Finset (BV n)} {s : BV n} (hs : s ≠ 0)
    (hQ : ∀ x ∈ Q, x + s ∉ Q) (x : BV n) :
    patch Q s (x + s) = patch Q s x := by
  have hcancel : x + s + s = x := add_add_cancel_bv x s
  by_cases h1 : x ∈ Q
  · have h2 : x + s ∉ Q := hQ x h1
    simp [patch, h1, h2, hcancel]
  · by_cases h2 : x + s ∈ Q
    · simp [patch, h1, h2]
    · have hne : x ≠ x + s := ne_add_of_ne_zero x hs
      have hene : ordIdx n x ≠ ordIdx n (x + s) := fun h => hne ((ordIdx n).injective h)
      by_cases h3 : ordIdx n x ≤ ordIdx n (x + s)
      · have h4 : ¬ (ordIdx n (x + s) ≤ ordIdx n x) := by
          intro h; exact hene (le_antisymm h3 h)
        simp [patch, h1, h2, h3, h4, hcancel]
      · have h4 : ordIdx n (x + s) ≤ ordIdx n x := le_of_not_ge h3
        simp [patch, h1, h2, h3, h4, hcancel]

