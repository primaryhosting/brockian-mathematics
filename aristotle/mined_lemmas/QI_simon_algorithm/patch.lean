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

noncomputable def patch {n : ℕ} (Q : Finset (BV n)) (s : BV n) (x : BV n) : BV n :=
  if x ∈ Q then x
  else if x + s ∈ Q then x + s
  else if ordIdx n x ≤ ordIdx n (x + s) then x else x + s

