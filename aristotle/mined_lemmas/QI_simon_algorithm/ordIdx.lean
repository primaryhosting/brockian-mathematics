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

noncomputable def ordIdx (n : ℕ) : BV n ≃ Fin (Fintype.card (BV n)) := Fintype.equivFin _

/-- Given a set `Q` of already-queried points containing at most one element of each coset
of `{0, s}`, this is a Simon function with hidden shift `s` that acts as the identity on `Q`. -/
