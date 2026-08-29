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

theorem ne_add_of_ne_zero {n : ℕ} (x : BV n) {s : BV n} (hs : s ≠ 0) : x ≠ x + s := by
  intro h
  apply hs
  funext i
  have h' : x i = x i + s i := congrFun h i
  have : ∀ a b : ZMod 2, a = a + b → b = 0 := by decide
  simpa using this (x i) (s i) h'

