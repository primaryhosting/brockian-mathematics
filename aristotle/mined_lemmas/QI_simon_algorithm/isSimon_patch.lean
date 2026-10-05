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

theorem isSimon_patch {n : ℕ} {Q : Finset (BV n)} {s : BV n} (hs : s ≠ 0)
    (hQ : ∀ x ∈ Q, x + s ∉ Q) : IsSimon s (patch Q s) := by
  intro x y
  constructor
  · intro h
    rcases patch_spec Q s x with hx | hx <;> rcases patch_spec Q s y with hy | hy
    · left; rw [← hx, ← hy, h]
    · right
      have : x = y + s := by rw [← hx, ← hy, h]
      rw [this, add_add_cancel_bv]
    · right
      have : x + s = y := by rw [← hx, ← hy, h]
      exact this.symm
    · left
      have : x + s = y + s := by rw [← hx, ← hy, h]
      have := congrArg (fun z => z + s) this
      simpa [add_add_cancel_bv] using this.symm
  · intro h
    rcases h with h | h
    · rw [h]
    · rw [h, patch_shift hs hQ]

/-- Simon instances exist for every nonzero hidden shift, so the statements above are not
vacuous. -/
