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

theorem ip_zero_left {n : ℕ} (y : BV n) : ip 0 y = 0 := by
  simp [ip]

/-! ## Quantum side: the interference pattern of a Simon query

After one query to `f` in superposition and a Hadamard transform, the (unnormalised)
amplitude of measuring the pair `(y, z)` is `∑_{x : f x = z} (-1)^{⟨x,y⟩}`. -/

/-- The sign character `χ : ZMod 2 → ℤ`, `χ a = (-1)^a`. -/
