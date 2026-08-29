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

theorem shift_determined_by_orthogonality {n : ℕ} (s t : BV n)
    (h : ∀ i : Fin n, (ip (Pi.single i 1) s = 0 ↔ ip (Pi.single i 1) t = 0)) : s = t := by
  funext i
  have hs : ip (Pi.single i (1 : ZMod 2)) s = s i := by
    simp [ip, Pi.single_apply]
  have ht : ip (Pi.single i (1 : ZMod 2)) t = t i := by
    simp [ip, Pi.single_apply]
  have := h i
  rw [hs, ht] at this
  revert this
  have : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact this (s i) (t i)

/-! ## Classical side: deterministic adaptive query algorithms -/

/-- A deterministic adaptive decision tree making at most `q` queries to a function
`BV n → BV n` and returning an element of `BV n`. -/
inductive DTree (n : ℕ) : ℕ → Type
  | leaf {q : ℕ} (out : BV n) : DTree n q
  | node {q : ℕ} (x : BV n) (k : BV n → DTree n q) : DTree n (q + 1)

/-- The output of the algorithm on the oracle `f`. -/
