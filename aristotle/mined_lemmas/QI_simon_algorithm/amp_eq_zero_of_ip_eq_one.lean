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

theorem amp_eq_zero_of_ip_eq_one {n : ℕ} {s : BV n} {f : BV n → BV n} (hf : IsSimon s f)
    {y : BV n} (hy : ip s y = 1) (z : BV n) : amp f y z = 0 := by
  have hs : s ≠ 0 := by
    intro h
    rw [h, ip_zero_left] at hy
    exact absurd hy (by decide)
  by_cases hz : ∃ x₀, f x₀ = z
  · obtain ⟨x₀, hx₀⟩ := hz
    have hne : x₀ ≠ x₀ + s := ne_add_of_ne_zero x₀ hs
    rw [amp, fiber_eq_pair hf hx₀, Finset.sum_pair hne, ip_add_left, hy]
    have : ∀ a : ZMod 2, chi a + chi (a + 1) = 0 := by decide
    exact this _
  · push_neg at hz
    have : Finset.univ.filter (fun x => f x = z) = (∅ : Finset (BV n)) := by
      ext w; simp [hz w]
    rw [amp, this, Finset.sum_empty]

/-- **Constructive interference.** Every outcome `y` orthogonal to the hidden shift, paired
with a value `z` in the range of `f`, has nonzero amplitude, so the measurement outcomes are
exactly the vectors orthogonal to `s`. -/
