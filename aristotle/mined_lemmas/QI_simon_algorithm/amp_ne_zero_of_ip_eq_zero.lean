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

theorem amp_ne_zero_of_ip_eq_zero {n : ℕ} {s : BV n} {f : BV n → BV n} (hf : IsSimon s f)
    (hs : s ≠ 0) {y : BV n} (hy : ip s y = 0) (x₀ : BV n) : amp f y (f x₀) ≠ 0 := by
  have hne : x₀ ≠ x₀ + s := ne_add_of_ne_zero x₀ hs
  rw [amp, fiber_eq_pair hf (rfl : f x₀ = f x₀), Finset.sum_pair hne, ip_add_left, hy]
  have : ∀ a : ZMod 2, chi a + chi (a + 0) ≠ 0 := by decide
  exact this _

/-- **`n` linear tests determine the hidden shift.** Hence the `O(n)` measurement outcomes
produced by the quantum algorithm suffice to identify `s`. -/
